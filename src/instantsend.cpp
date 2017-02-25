// Copyright (c) 2014-2017 The Dash Core Developers
// Copyright (c) 2015-2017 Silk Network Developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "instantsend.h"

#include "activestormnode.h"
#include "key.h"
#include "main.h"
#include "net.h"
#include "privatesend.h"
#include "protocol.h"
#include "spork.h"
#include "stormnode-sync.h"
#include "stormnodeman.h"
#include "sync.h"
#include "txmempool.h"
#include "util.h"
#include "consensus/validation.h"

#include <boost/algorithm/string/replace.hpp>
#include <boost/thread.hpp>

extern CWallet* pwalletMain;
extern CTxMemPool mempool;

bool fEnableInstantSend = true;
int nInstantSendDepth = DEFAULT_INSTANTSEND_DEPTH;
int nCompleteTXLocks;

CInstantSend instantsend;

// Transaction Locks
//
// step 2) Top INSTANTSEND_SIGNATURES_TOTAL Stormnodes push "txvote" message
// step 2) Top COutPointLock::SIGNATURES_TOTAL Stormnodes per each spent outpoint push "txvote" message
// step 3) Once there are COutPointLock::SIGNATURES_REQUIRED valid "txvote" messages per each spent outpoint
//         for a corresponding "txlreg" message, all outpoints from that tx are treated as locked

//
// CInstantSend
//
void CInstantSend::ProcessMessage(CNode* pfrom, std::string& strCommand, CDataStream& vRecv)
{
    if(fLiteMode) return; // disable all DarkSilk specific functionality
    if(!sporkManager.IsSporkActive(SPORK_2_INSTANTSEND_ENABLED)) return;

    // Ignore any InstantSend messages until Stormnode list is synced
    if(!stormnodeSync.IsStormnodeListSynced()) return;

    // NOTE: NetMsgType::TXLOCKREQUEST is handled via ProcessMessage() in main.cpp
    if (strCommand == NetMsgType::TXLOCKVOTE) // InstantSend Transaction Lock Consensus Votes
    {
        if(pfrom->nVersion < MIN_INSTANTSEND_PROTO_VERSION) return;

        CTxLockVote vote;
        vRecv >> vote;

        LOCK2(cs_main, cs_instantsend);

        uint256 nVoteHash = vote.GetHash();

        if(mapTxLockVotes.count(nVoteHash)) return;
        mapTxLockVotes.insert(std::make_pair(nVoteHash, vote));

        ProcessTxLockVote(pfrom, vote);

        return;
    }
}

bool CInstantSend::ProcessTxLockRequest(const CTxLockRequest& txLockRequest)
{
    LOCK2(cs_main, cs_instantsend);


    uint256 txHash = txLockRequest.GetHash();

    // Check to see if we conflict with existing completed lock,
    // fail if so, there can't be 2 completed locks for the same outpoint
    BOOST_FOREACH(const CTxIn& txin, txLockRequest.vin) {
        std::map<COutPoint, uint256>::iterator it = mapLockedOutpoints.find(txin.prevout);
        if(it != mapLockedOutpoints.end()) {
            // Conflicting with complete lock, ignore this one
            // (this could be the one we have but we don't want to try to lock it twice anyway)
            LogPrintf("CInstantSend::ProcessTxLockRequest -- WARNING: Found conflicting completed Transaction Lock, skipping current one, txid=%s, completed lock txid=%s\n",
                    txLockRequest.GetHash().ToString(), it->second.ToString());
            return false;
        }
    }

    // Check to see if there are votes for conflicting request,
    // if so - do not fail, just warn user
    BOOST_FOREACH(const CTxIn& txin, txLockRequest.vin) {
        std::map<COutPoint, std::set<uint256> >::iterator it = mapVotedOutpoints.find(txin.prevout);
        if(it != mapVotedOutpoints.end()) {
            BOOST_FOREACH(const uint256& hash, it->second) {
                if(hash != txLockRequest.GetHash()) {
                    LogPrint("instantsend", "CInstantSend::ProcessTxLockRequest -- Double spend attempt! %s\n", txin.prevout.ToStringShort());
                    // do not fail here, let it go and see which one will get the votes to be locked
                }
            }
        }
    }

    if(!CreateTxLockCandidate(txLockRequest)) {

     // smth is not right
        LogPrintf("CInstantSend::ProcessTxLockRequest -- CreateTxLockCandidate failed, txid=%s\n", txHash.ToString());
     return false;
 }
    LogPrintf("CInstantSend::ProcessTxLockRequest -- accepted, txid=%s\n", txHash.ToString());

    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    CTxLockCandidate& txLockCandidate = itLockCandidate->second;
    Vote(txLockCandidate);

 ProcessOrphanTxLockVotes();

    // Stormnodes will sometimes propagate votes before the transaction is known to the client.
    // If this just happened - lock inputs, resolve conflicting locks, update transaction status
    // forcing external script notification.
    if(IsInstantSendReadyToLock(txHash)) {
        if(ResolveConflicts(txLockCandidate)) {
            // the order here matters
            UpdateLockedTransaction(txLockCandidate, true);
            LockTransactionInputs(txLockCandidate);
        }
    }

 return true;
}

bool CInstantSend::CreateTxLockCandidate(const CTxLockRequest& txLockRequest)
{
    // Normally we should require all outpoints to be unspent, but in case we are reprocessing
    // because of a lot of legit orphan votes we should also check already spent outpoints.
    uint256 txHash = txLockRequest.GetHash();
    if(!txLockRequest.IsValid(IsEnoughOrphanVotesForTx(txLockRequest))) return false;

    LOCK(cs_instantsend);

    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    if(itLockCandidate == mapTxLockCandidates.end()) {
        LogPrintf("CInstantSend::CreateTxLockCandidate -- new, txid=%s\n", txHash.ToString());

        CTxLockCandidate txLockCandidate(txLockRequest);
        // all inputs should already be checked by txLockRequest.IsValid() above, just use them now
        BOOST_REVERSE_FOREACH(const CTxIn& txin, txLockRequest.vin) {
            txLockCandidate.AddOutPointLock(txin.prevout);
        }
        mapTxLockCandidates.insert(std::make_pair(txHash, txLockCandidate));
    } else {
        LogPrint("instantsend", "CInstantSend::CreateTxLockCandidate -- seen, txid=%s\n", txHash.ToString());
    }
    return true;

}

void CInstantSend::Vote(CTxLockCandidate& txLockCandidate)
{
    if(!fStormNode) return;

    LOCK2(cs_main, cs_instantsend);

    uint256 txHash = txLockCandidate.GetHash();
    // check if we need to vote on this candidate's outpoints,
    // it's possible that we need to vote for several of them
    std::map<COutPoint, COutPointLock>::iterator itOutpointLock = txLockCandidate.mapOutPointLocks.begin();
    while(itOutpointLock != txLockCandidate.mapOutPointLocks.end()) {

        int nPrevoutHeight = GetUTXOHeight(itOutpointLock->first);
        if(nPrevoutHeight == -1) {
            LogPrint("instantsend", "CInstantSend::Vote -- Failed to find UTXO %s\n", itOutpointLock->first.ToStringShort());
            return;
        }

        int nLockInputHeight = nPrevoutHeight + 4;

        int n = snodeman.GetStormnodeRank(activeStormnode.vin, nLockInputHeight, MIN_INSTANTSEND_PROTO_VERSION);

        if(n == -1) {
            LogPrint("instantsend", "CInstantSend::Vote -- Unknown Stormnode %s\n", activeStormnode.vin.prevout.ToStringShort());
            ++itOutpointLock;
            continue;
        }

        int nSignaturesTotal = COutPointLock::SIGNATURES_TOTAL;
        if(n > nSignaturesTotal) {
            LogPrint("instantsend", "CInstantSend::Vote -- Stormnode not in the top %d (%d)\n", nSignaturesTotal, n);
            ++itOutpointLock;
            continue;
        }

        LogPrint("instantsend", "CInstantSend::Vote -- In the top %d (%d)\n", nSignaturesTotal, n);

        std::map<COutPoint, std::set<uint256> >::iterator itVoted = mapVotedOutpoints.find(itOutpointLock->first);

        // Check to see if we already voted for this outpoint,
        // refuse to vote twice or to include the same outpoint in another tx
        bool fAlreadyVoted = false;
        if(itVoted != mapVotedOutpoints.end()) {
            BOOST_FOREACH(const uint256& hash, itVoted->second) {
                std::map<uint256, CTxLockCandidate>::iterator it2 = mapTxLockCandidates.find(hash);
                if(it2->second.HasStormnodeVoted(itOutpointLock->first, activeStormnode.vin.prevout)) {
                    // we already voted for this outpoint to be included either in the same tx or in a competing one,
                    // skip it anyway
                    fAlreadyVoted = true;
                    LogPrintf("CInstantSend::Vote -- WARNING: We already voted for this outpoint, skipping: txHash=%s, outpoint=%s\n",
                            txHash.ToString(), itOutpointLock->first.ToStringShort());
                    break;
                }
            }
        }
        if(fAlreadyVoted) {
            ++itOutpointLock;
            continue; // skip to the next outpoint
        }

        // we haven't voted for this outpoint yet, let's try to do this now
        CTxLockVote vote(txHash, itOutpointLock->first, activeStormnode.vin.prevout);

        if(!vote.Sign()) {
            LogPrintf("CInstantSend::Vote -- Failed to sign consensus vote\n");
            return;
        }
        if(!vote.CheckSignature()) {
            LogPrintf("CInstantSend::Vote -- Signature invalid\n");
            return;
        }

        // vote constructed sucessfully, let's store and relay it
        uint256 nVoteHash = vote.GetHash();
        mapTxLockVotes.insert(std::make_pair(nVoteHash, vote));
        if(itOutpointLock->second.AddVote(vote)) {
            LogPrintf("CInstantSend::Vote -- Vote created successfully, relaying: txHash=%s, outpoint=%s, vote=%s\n",
                    txHash.ToString(), itOutpointLock->first.ToStringShort(), nVoteHash.ToString());

            if(itVoted == mapVotedOutpoints.end()) {
                std::set<uint256> setHashes;
                setHashes.insert(txHash);
                mapVotedOutpoints.insert(std::make_pair(itOutpointLock->first, setHashes));
            } else {
                mapVotedOutpoints[itOutpointLock->first].insert(txHash);
                if(mapVotedOutpoints[itOutpointLock->first].size() > 1) {
                    // it's ok to continue, just warn user
                    LogPrintf("CInstantSend::Vote -- WARNING: Vote conflicts with some existing votes: txHash=%s, outpoint=%s, vote=%s\n",
                            txHash.ToString(), itOutpointLock->first.ToStringShort(), nVoteHash.ToString());
                }
            }

            vote.Relay();
        }

        ++itOutpointLock;
    }
}

//received a consensus vote
bool CInstantSend::ProcessTxLockVote(CNode* pfrom, CTxLockVote& vote)
{
    LOCK2(cs_main, cs_instantsend);

    uint256 txHash = vote.GetTxHash();

    if(!vote.IsValid(pfrom)) {
        // could be because of missing SN
        LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Vote is invalid, txid=%s\n", txHash.ToString());
        return false;
    }

    // Stormnodes will sometimes propagate votes before the transaction is known to the client,
    // will actually process only after the lock request itself has arrived

    std::map<uint256, CTxLockCandidate>::iterator it = mapTxLockCandidates.find(txHash);
    if(it == mapTxLockCandidates.end()) {
        if(!mapTxLockVotesOrphan.count(vote.GetHash())) {
            mapTxLockVotesOrphan[vote.GetHash()] = vote;
            LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Orphan vote: txid=%s  stormnode=%s new\n",
                    txHash.ToString(), vote.GetStormnodeOutpoint().ToStringShort());
            bool fReprocess = true;
            std::map<uint256, CTxLockRequest>::iterator itLockRequest = mapLockRequestAccepted.find(txHash);
            if(itLockRequest == mapLockRequestAccepted.end()) {
                itLockRequest = mapLockRequestRejected.find(txHash);
                if(itLockRequest == mapLockRequestRejected.end()) {
                    // still too early, wait for tx lock request
                    fReprocess = false;
                }
            }
            if(fReprocess && IsEnoughOrphanVotesForTx(itLockRequest->second)) {
                // We have enough votes for corresponding lock to complete,
                // tx lock request should already be received at this stage.
                LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Found enough orphan votes, reprocessing Transaction Lock Request: txid=%s\n", txHash.ToString());
                ProcessTxLockRequest(itLockRequest->second);
                return true;
            }
        } else {
            LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Orphan vote: txid=%s  stormnode=%s seen\n",
                    txHash.ToString(), vote.GetStormnodeOutpoint().ToStringShort());
        }

        // This tracks those messages and allows only the same rate as of the rest of the network
        // TODO: make sure this works good enough for multi-quorum
        int nStormnodeOrphanExpireTime = GetTime() + 60*10; // keep time data for 10 minutes
        if(!mapStormnodeOrphanVotes.count(vote.GetStormnodeOutpoint())) {
            mapStormnodeOrphanVotes[vote.GetStormnodeOutpoint()] = nStormnodeOrphanExpireTime;
        } else {
            int64_t nPrevOrphanVote = mapStormnodeOrphanVotes[vote.GetStormnodeOutpoint()];
            if(nPrevOrphanVote > GetTime() && nPrevOrphanVote > GetAverageStormnodeOrphanVoteTime()) {
                LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- stormnode is spamming orphan Transaction Lock Votes: txid=%s  stormnode=%s\n",
                        txHash.ToString(), vote.GetStormnodeOutpoint().ToStringShort());
                // Misbehaving(pfrom->id, 1);
                return false;
            }
            // not spamming, refresh
            mapStormnodeOrphanVotes[vote.GetStormnodeOutpoint()] = nStormnodeOrphanExpireTime;
        }

        return true;
    }

    LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Transaction Lock Vote, txid=%s\n", txHash.ToString());
    std::map<COutPoint, std::set<uint256> >::iterator it1 = mapVotedOutpoints.find(vote.GetOutpoint());
    if(it1 != mapVotedOutpoints.end()) {
        BOOST_FOREACH(const uint256& hash, it1->second) {
            if(hash != txHash) {
                // same outpoint was already voted to be locked by another tx lock request,
                // find out if the same mn voted on this outpoint before
                std::map<uint256, CTxLockCandidate>::iterator it2 = mapTxLockCandidates.find(hash);
                if(it2->second.HasStormnodeVoted(vote.GetOutpoint(), vote.GetStormnodeOutpoint())) {
                    // yes, it did, refuse to accept a vote to include the same outpoint in another tx
                    // from the same stormnode.
                    // TODO: apply pose ban score to this stormnode?
                    // NOTE: if we decide to apply pose ban score here, this vote must be relayed further
                    // to let all other nodes know about this node's misbehaviour and let them apply
                    // pose ban score too.
                    LogPrintf("CInstantSend::ProcessTxLockVote -- stormnode sent conflicting votes! %s\n", vote.GetStormnodeOutpoint().ToStringShort());
                    return false;
                }
            }
        }        
        // we have votes by other stormnodes only (so far), let's continue and see who will win
    } else {
        std::set<uint256> setHashes;
        setHashes.insert(txHash);
        mapVotedOutpoints.insert(std::make_pair(vote.GetOutpoint(), setHashes));
    }

    if(!it->second.AddVote(vote)) {
        // this should never happen

        return false;
    }

    int nSignatures = it->second.CountVotes();
    int nSignaturesMax = it->second.txLockRequest.GetMaxSignatures();
    LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Transaction Lock signatures count: %d/%d, vote hash=%s\n",
            nSignatures, nSignaturesMax, vote.GetHash().ToString());
    if(it->second.IsAllOutPointsReady()) {
        // we have enough votes now
        LogPrint("instantsend", "CInstantSend::ProcessTxLockVote -- Transaction Lock Is Complete! txid=%s\n", txHash.ToString());
        if(ResolveConflicts(it->second)) {
            // the order here matters
            UpdateLockedTransaction(it->second);
            if(!IsLockedInstantSendTransaction(txHash)) {
                LockTransactionInputs(it->second);
            }
        }
    }
    vote.Relay();

    return true;
}

void CInstantSend::ProcessOrphanTxLockVotes()
{
    LOCK2(cs_main, cs_instantsend);
    std::map<uint256, CTxLockVote>::iterator it = mapTxLockVotesOrphan.begin();
    while(it != mapTxLockVotesOrphan.end()) {
        if(ProcessTxLockVote(NULL, it->second)) {
            mapTxLockVotesOrphan.erase(it++);
        } else {
            ++it;
        }
    }
}

bool CInstantSend::IsEnoughOrphanVotesForTx(const CTxLockRequest& txLockRequest)
{
    // There could be a situation when we already have quite a lot of votes
    // but tx lock request still wasn't received. Let's scan through
    // orphan votes to check if this is the case.
    BOOST_FOREACH(const CTxIn& txin, txLockRequest.vin) {
        if(!IsEnoughOrphanVotesForTxAndOutPoint(txLockRequest.GetHash(), txin.prevout)) {
            return false;
        }
    }
    return true;
}

bool CInstantSend::IsEnoughOrphanVotesForTxAndOutPoint(const uint256& txHash, const COutPoint& outpoint)
{
    // Scan orphan votes to check if this outpoint has enough orphan votes to be locked in some tx.
    LOCK2(cs_main, cs_instantsend);
    int nCountVotes = 0;
    std::map<uint256, CTxLockVote>::iterator it = mapTxLockVotesOrphan.begin();
    while(it != mapTxLockVotesOrphan.end()) {
        if(it->second.GetTxHash() == txHash && it->second.GetOutpoint() == outpoint) {
            nCountVotes++;
            if(nCountVotes >= COutPointLock::SIGNATURES_REQUIRED) {
                return true;
            }
        }
        ++it;
    }
    return false;
}

void CInstantSend::UpdateLockedTransaction(CTxLockCandidate& txLockCandidate, bool fForceNotification)
{
    LOCK(cs_instantsend);

    uint256 txHash = txLockCandidate.GetHash();

    // either notification was forced or we are just about to lock tx inputs,
    // lock candidate must be ready in either case
    bool fNotify = (fForceNotification || !IsLockedInstantSendTransaction(txHash)) &&
                    txLockCandidate.IsAllOutPointsReady();

#ifdef ENABLE_WALLET
    if(pwalletMain && pwalletMain->UpdatedTransaction(txHash)) {
        // bumping this to update UI
        nCompleteTXLocks++;
        if(fNotify) {
            // notify an external script once threshold is reached
            std::string strCmd = GetArg("-instantsendnotify", "");
            if(!strCmd.empty()) {
                boost::replace_all(strCmd, "%s", txHash.GetHex());
                boost::thread t(runCommand, strCmd); // thread runs free
            }
        }
    }
#endif

    if(fNotify)
        GetMainSignals().NotifyTransactionLock(txLockCandidate.txLockRequest);
}

void CInstantSend::LockTransactionInputs(const CTxLockCandidate& txLockCandidate)
{
    LOCK(cs_instantsend);

    uint256 txHash = txLockCandidate.GetHash();

    if(!txLockCandidate.IsAllOutPointsReady()) return;

    std::map<COutPoint, COutPointLock>::const_iterator it = txLockCandidate.mapOutPointLocks.begin();

    while(it != txLockCandidate.mapOutPointLocks.end()) {
        mapLockedOutpoints.insert(std::make_pair(it->first, txHash));
        ++it;
    }
}

bool CInstantSend::GetLockedOutPointTxHash(const COutPoint& outpoint, uint256& hashRet)
{
    LOCK(cs_instantsend);
    std::map<COutPoint, uint256>::iterator it = mapLockedOutpoints.find(outpoint);
    if(it == mapLockedOutpoints.end()) return false;
    hashRet = it->second;
    return true;
}

bool CInstantSend::ResolveConflicts(const CTxLockCandidate& txLockCandidate)
{
    LOCK2(cs_main, cs_instantsend);

    uint256 txHash = txLockCandidate.GetHash();

    // make sure the lock is ready
    if(!txLockCandidate.IsAllOutPointsReady()) return true; // not an error

    LOCK(mempool.cs); // protect mempool.mapNextTx, mempool.mapTx

    bool fMempoolConflict = false;

    BOOST_FOREACH(const CTxIn& txin, txLockCandidate.txLockRequest.vin) {
        uint256 hashLocked;
        if(GetLockedOutPointTxHash(txin.prevout, hashLocked) && txHash != hashLocked) {
            // conflicting with complete lock, ignore current one
            LogPrintf("CInstantSend::ResolveConflicts -- WARNING: Found conflicting completed Transaction Lock, skipping current one, txid=%s, conflicting txid=%s\n",
                    txHash.ToString(), hashLocked.ToString());
            return false; // can't/shouldn't do anything
        } else if (mempool.mapNextTx.count(txin.prevout)) {
            // conflicting with tx in mempool
            fMempoolConflict = true;
            const CTransaction *ptxConflicting = mempool.mapNextTx[txin.prevout].ptx;
            uint256 hashConflicting = ptxConflicting->GetHash();
            if(HasTxLockRequest(hashConflicting)) {
                // There can be only one completed lock, the other lock request should never complete,
                // remove it from mempool and try to accept this (completed) one to mempool.
                LogPrintf("CInstantSend::ResolveConflicts -- WARNING: Found conflicting Transaction Lock Request, replacing by completed Transaction Lock, txid=%s, conflicting txid=%s\n",
                        txHash.ToString(), hashConflicting.ToString());
            } else {
                // If this lock is completed, we don't really care about normal conflicting txes.
                LogPrintf("CInstantSend::ResolveConflicts -- WARNING: Found conflicting transaction, replacing by completed Transaction Lock, txid=%s, conflicting txid=%s\n",
                        txHash.ToString(), hashConflicting.ToString());
            }
        }
    } // FOREACH
    if(fMempoolConflict) {
        std::list<CTransaction> removed;
        // remove every tx conflicting with current Transaction Lock Request
        mempool.removeConflicts(txLockCandidate.txLockRequest, removed);
        // and try to accept it in mempool again
        CValidationState state;
        bool fMissingInputs = false;
        if(!AcceptToMemoryPool(mempool, state, txLockCandidate.txLockRequest, true, &fMissingInputs)) {
            LogPrintf("CInstantSend::ResolveConflicts -- ERROR: Failed to accept completed Transaction Lock to mempool, txid=%s\n", txHash.ToString());
            return false;
        }
        LogPrintf("CInstantSend::ResolveConflicts -- Accepted completed Transaction Lock, txid=%s\n", txHash.ToString());
        return true;
    }
    // No conflicts were found so far, check to see if it was already included in block
    CTransaction txTmp;
    uint256 hashBlock;
    if(GetTransaction(txHash, txTmp, Params().GetConsensus(), hashBlock, true) && hashBlock != uint256()) {
        LogPrint("instantsend", "CInstantSend::ResolveConflicts -- Done, %s is included in block %s\n", txHash.ToString(), hashBlock.ToString());
        return true;
    }
    // Not in block yet, make sure all its inputs are still unspent
    BOOST_FOREACH(const CTxIn& txin, txLockCandidate.txLockRequest.vin) {
        CCoins coins;
        if(!pcoinsTip->GetCoins(txin.prevout.hash, coins) ||
           (unsigned int)txin.prevout.n>=coins.vout.size() ||
           coins.vout[txin.prevout.n].IsNull()) {
            // Not in UTXO anymore? Either this lock or conflicting tx was mined while we were waiting for votes.
            // Reprocess tip to make sure tx for this lock was included.
            //
            LogPrintf("CTxLockRequest::ResolveConflicts -- Failed to find UTXO %s - disconnecting tip...\n", txin.prevout.ToStringShort());
            if(!DisconnectBlocks(1)) {
                return false;
            }
            // Recursively check at "new" old height. Conflicting tx should be rejected by AcceptToMemoryPool.
            ResolveConflicts(txLockCandidate);
            LogPrintf("CTxLockRequest::ResolveConflicts -- Failed to find UTXO %s - activating best chain...\n", txin.prevout.ToStringShort());
            // Activate best chain, block which includes conflicting tx should be rejected by ConnectBlock.
            CValidationState state;
            if(!ActivateBestChain(state, Params()) || !state.IsValid()) {
                LogPrintf("CTxLockRequest::ResolveConflicts -- ActivateBestChain failed, txid=%s\n", txin.prevout.ToStringShort());
                return false;
            }
            LogPrintf("CTxLockRequest::ResolveConflicts -- Failed to find UTXO %s - fixed!\n", txin.prevout.ToStringShort());
        }
    }
    LogPrint("instantsend", "CInstantSend::ResolveConflicts -- Done, txid=%s\n", txHash.ToString());

    return true;
}

int64_t CInstantSend::GetAverageStormnodeOrphanVoteTime()
{
    LOCK(cs_instantsend);
    // NOTE: should never actually call this function when mapStormnodeOrphanVotes is empty
    if(mapStormnodeOrphanVotes.empty()) return 0;

    std::map<COutPoint, int64_t>::iterator it = mapStormnodeOrphanVotes.begin();
    int64_t total = 0;

    while(it != mapStormnodeOrphanVotes.end()) {
        total+= it->second;
        ++it;
    }

    return total / mapStormnodeOrphanVotes.size();
}

void CInstantSend::CheckAndRemove()
{
    if(!pCurrentBlockIndex) return;

    LOCK(cs_instantsend);

    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.begin();

    // remove expired candidates
    while(itLockCandidate != mapTxLockCandidates.end()) {
        CTxLockCandidate &txLockCandidate = itLockCandidate->second;
        uint256 txHash = txLockCandidate.GetHash();
        if(txLockCandidate.IsExpired(pCurrentBlockIndex->nHeight)) {
            LogPrintf("CInstantSend::CheckAndRemove -- Removing expired Transaction Lock Candidate: txid=%s\n", txHash.ToString());
            std::map<COutPoint, COutPointLock>::iterator itOutpointLock = txLockCandidate.mapOutPointLocks.begin();
            while(itOutpointLock != txLockCandidate.mapOutPointLocks.end()) {
                mapLockedOutpoints.erase(itOutpointLock->first);
                mapVotedOutpoints.erase(itOutpointLock->first);
                ++itOutpointLock;
            }
            mapLockRequestAccepted.erase(txHash);
            mapLockRequestRejected.erase(txHash);
            mapTxLockCandidates.erase(itLockCandidate++);
        } else {
            ++itLockCandidate;
        }
    }
    // remove expired votes
    std::map<uint256, CTxLockVote>::iterator itVote = mapTxLockVotes.begin();
    while(itVote != mapTxLockVotes.end()) {
        if(itVote->second.IsExpired(pCurrentBlockIndex->nHeight)) {
            LogPrint("instantsend", "CInstantSend::CheckAndRemove -- Removing expired vote: txid=%s  stormnode=%s\n",
                    itVote->second.GetTxHash().ToString(), itVote->second.GetStormnodeOutpoint().ToStringShort());
            mapTxLockVotes.erase(itVote++);        } else {
            ++itVote;
        }
    }

    // remove expired orphan votes
    std::map<uint256, CTxLockVote>::iterator itOrphanVote = mapTxLockVotesOrphan.begin();
    while(itOrphanVote != mapTxLockVotesOrphan.end()) {
        if(GetTime() - itOrphanVote->second.GetTimeCreated() > ORPHAN_VOTE_SECONDS) {
            LogPrint("instantsend", "CInstantSend::CheckAndRemove -- Removing expired orphan vote: txid=%s  stormnode=%s\n",
                    itOrphanVote->second.GetTxHash().ToString(), itOrphanVote->second.GetStormnodeOutpoint().ToStringShort());
            mapTxLockVotes.erase(itOrphanVote->first);
            mapTxLockVotesOrphan.erase(itOrphanVote++);
        } else {
            ++itOrphanVote;
        }
    }

    // remove expired stormnode orphan votes (DOS protection)
    std::map<COutPoint, int64_t>::iterator itStormnodeOrphan = mapStormnodeOrphanVotes.begin();
    while(itStormnodeOrphan != mapStormnodeOrphanVotes.end()) {
        if(itStormnodeOrphan->second < GetTime()) {
            LogPrint("instantsend", "CInstantSend::CheckAndRemove -- Removing expired orphan stormnode vote: stormnode=%s\n",
                    itStormnodeOrphan->first.ToStringShort());
            mapStormnodeOrphanVotes.erase(itStormnodeOrphan++);
        } else {
            ++itStormnodeOrphan;
        }
    }
}

bool CInstantSend::AlreadyHave(const uint256& hash)
{
    LOCK(cs_instantsend);
    return mapLockRequestAccepted.count(hash) ||
            mapLockRequestRejected.count(hash) ||
            mapTxLockVotes.count(hash);
}


void CInstantSend::AcceptLockRequest(const CTxLockRequest& txLockRequest)
{
    mapLockRequestAccepted.insert(make_pair(txLockRequest.GetHash(), txLockRequest));
}

void CInstantSend::RejectLockRequest(const CTxLockRequest& txLockRequest)
{
    mapLockRequestRejected.insert(make_pair(txLockRequest.GetHash(), txLockRequest));
}

bool CInstantSend::HasTxLockRequest(const uint256& txHash)
{
    CTxLockRequest txLockRequestTmp;
    return GetTxLockRequest(txHash, txLockRequestTmp);
}

bool CInstantSend::GetTxLockRequest(const uint256& txHash, CTxLockRequest& txLockRequestRet)
{
    LOCK(cs_instantsend);

    std::map<uint256, CTxLockCandidate>::iterator it = mapTxLockCandidates.find(txHash);
    if(it == mapTxLockCandidates.end()) return false;
    txLockRequestRet = it->second.txLockRequest;

    return true;
}

bool CInstantSend::GetTxLockVote(const uint256& hash, CTxLockVote& txLockVoteRet)
{
    LOCK(cs_instantsend);

    std::map<uint256, CTxLockVote>::iterator it = mapTxLockVotes.find(hash);
    if(it == mapTxLockVotes.end()) return false;
    txLockVoteRet = it->second;

    return true;
}

bool CInstantSend::IsInstantSendReadyToLock(const uint256& txHash)
{
    if(!fEnableInstantSend || fLargeWorkForkFound || fLargeWorkInvalidChainFound ||
        !sporkManager.IsSporkActive(SPORK_2_INSTANTSEND_ENABLED)) return false;

    LOCK(cs_instantsend);
    // There must be a successfully verified lock request
    // and all outputs must be locked (i.e. have enough signatures)
    std::map<uint256, CTxLockCandidate>::iterator it = mapTxLockCandidates.find(txHash);
    return it != mapTxLockCandidates.end() && it->second.IsAllOutPointsReady();
}

bool CInstantSend::IsLockedInstantSendTransaction(const uint256& txHash)
{
    if(!fEnableInstantSend || fLargeWorkForkFound || fLargeWorkInvalidChainFound ||
        !sporkManager.IsSporkActive(SPORK_2_INSTANTSEND_ENABLED)) return false;

    LOCK(cs_instantsend);

    // there must be a lock candidate
    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    if(itLockCandidate == mapTxLockCandidates.end()) return false;

    // which should have outpoints
    if(itLockCandidate->second.mapOutPointLocks.empty()) return false;

    // and all of these outputs must be included in mapLockedOutpoints with correct hash
    std::map<COutPoint, COutPointLock>::iterator itOutpointLock = itLockCandidate->second.mapOutPointLocks.begin();
    while(itOutpointLock != itLockCandidate->second.mapOutPointLocks.end()) {
        uint256 hashLocked;
        if(!GetLockedOutPointTxHash(itOutpointLock->first, hashLocked) || hashLocked != txHash) return false;
        ++itOutpointLock;
    }

    return true;
}

int CInstantSend::GetTransactionLockSignatures(const uint256& txHash)
{
    if(!fEnableInstantSend) return -1;
    if(fLargeWorkForkFound || fLargeWorkInvalidChainFound) return -2;
    if(!sporkManager.IsSporkActive(SPORK_2_INSTANTSEND_ENABLED)) return -3;

    LOCK(cs_instantsend);

    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    if(itLockCandidate != mapTxLockCandidates.end()) {
        return itLockCandidate->second.CountVotes();
    }

    return -1;
}

bool CInstantSend::IsTxLockRequestTimedOut(const uint256& txHash)
{
    if(!fEnableInstantSend) return false;

    LOCK(cs_instantsend);

    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    if (itLockCandidate != mapTxLockCandidates.end()) {
        return !itLockCandidate->second.IsAllOutPointsReady() &&
                itLockCandidate->second.txLockRequest.IsTimedOut();
    }

    return false;
}

void CInstantSend::Relay(const uint256& txHash) const
{
    std::map<uint256, CTxLockCandidate>::const_iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    if (itLockCandidate != mapTxLockCandidates.end()) {
        itLockCandidate->second.Relay();
    }
}

void CInstantSend::UpdatedBlockTip(const CBlockIndex *pindex){
    pCurrentBlockIndex = pindex;
}

void CInstantSend::SyncTransaction(const CTransaction& tx, const CBlock* pblock)
{
    // Update lock candidates and votes if corresponding tx confirmed
    // or went from confirmed to 0-confirmed or conflicted.

    if (tx.IsCoinBase()) return;

    LOCK2(cs_main, cs_instantsend);

    uint256 txHash = tx.GetHash();

    // When tx is 0-confirmed or conflicted, pblock is NULL and nHeightNew should be set to -1
    CBlockIndex* pblockindex = pblock ? mapBlockIndex[pblock->GetHash()] : NULL;
    int nHeightNew = pblockindex ? pblockindex->nHeight : -1;

    LogPrint("instantsend", "CInstantSend::SyncTransaction -- txid=%s nHeightNew=%d\n", txHash.ToString(), nHeightNew);

    // Check lock candidates
    std::map<uint256, CTxLockCandidate>::iterator itLockCandidate = mapTxLockCandidates.find(txHash);
    if(itLockCandidate != mapTxLockCandidates.end()) {
        LogPrint("instantsend", "CInstantSend::SyncTransaction -- txid=%s nHeightNew=%d lock candidate updated\n",
                txHash.ToString(), nHeightNew);
        itLockCandidate->second.SetConfirmedHeight(nHeightNew);
        // Loop through outpoint locks
        std::map<COutPoint, COutPointLock>::iterator itOutpointLock = itLockCandidate->second.mapOutPointLocks.begin();
        while(itOutpointLock != itLockCandidate->second.mapOutPointLocks.end()) {
            // Check corresponding lock votes
            std::vector<CTxLockVote> vVotes = itOutpointLock->second.GetVotes();
            std::vector<CTxLockVote>::iterator itVote = vVotes.begin();
            std::map<uint256, CTxLockVote>::iterator it;
            while(itVote != vVotes.end()) {
                uint256 nVoteHash = itVote->GetHash();
                LogPrint("instantsend", "CInstantSend::SyncTransaction -- txid=%s nHeightNew=%d vote %s updated\n",
                        txHash.ToString(), nHeightNew, nVoteHash.ToString());
                it = mapTxLockVotes.find(nVoteHash);
                if(it != mapTxLockVotes.end()) {
                    it->second.SetConfirmedHeight(nHeightNew);
                }
                ++itVote;
            }
            ++itOutpointLock;
        }
    }

    // check orphan votes
    std::map<uint256, CTxLockVote>::iterator itOrphanVote = mapTxLockVotesOrphan.begin();
    while(itOrphanVote != mapTxLockVotesOrphan.end()) {
        if(itOrphanVote->second.GetTxHash() == txHash) {
            LogPrint("instantsend", "CInstantSend::SyncTransaction -- txid=%s nHeightNew=%d vote %s updated\n",
                    txHash.ToString(), nHeightNew, itOrphanVote->first.ToString());
            mapTxLockVotes[itOrphanVote->first].SetConfirmedHeight(nHeightNew);
        }
        ++itOrphanVote;
    }
}

//
// CTxLockRequest
//

bool CTxLockRequest::IsValid(bool fRequireUnspent) const
{
    if(vout.size() < 1) return false;

    if(vin.size() > WARN_MANY_INPUTS) {
        LogPrint("instantsend", "CTxLockRequest::IsValid -- WARNING: Too many inputs: tx=%s", ToString());
        return false;
    }

    LOCK(cs_main);
    if(!CheckFinalTx(*this)) {
        LogPrint("instantsend", "CTxLockRequest::IsValid -- Transaction is not final: tx=%s", ToString());
        return false;
    }

    int64_t nValueIn = 0;
    int64_t nValueOut = 0;

    BOOST_FOREACH(const CTxOut& txout, vout) {
        // InstantSend supports normal scripts and unspendable (i.e. data) scripts.
        // TODO: Look into other script types that are normal and can be included
        if(!txout.scriptPubKey.IsNormalPaymentScript() && !txout.scriptPubKey.IsUnspendable()) {
            LogPrint("instantsend", "CTxLockRequest::IsValid -- Invalid Script %s", ToString());
            return false;
        }
        nValueOut += txout.nValue;
    }

    BOOST_FOREACH(const CTxIn& txin, vin) {

        CCoins coins;
        int nPrevoutHeight = 0;
        if(!pcoinsTip->GetCoins(txin.prevout.hash, coins) ||
           (unsigned int)txin.prevout.n>=coins.vout.size() ||
           coins.vout[txin.prevout.n].IsNull()) {
            LogPrint("instantsend", "CTxLockRequest::IsValid -- Failed to find UTXO %s\n", txin.prevout.ToStringShort());
            // Normally above sould be enough, but in case we are reprocessing this because of
            // a lot of legit orphan votes we should also check already spent outpoints.
            if(!fRequireUnspent) return false;
            CTransaction txOutpointCreated;
            uint256 nHashOutpointConfirmed;
            if(!GetTransaction(txin.prevout.hash, txOutpointCreated, Params().GetConsensus(), nHashOutpointConfirmed, true) || nHashOutpointConfirmed == uint256()) {
                LogPrint("instantsend", "txLockRequest::IsValid -- Failed to find outpoint %s\n", txin.prevout.ToStringShort());
                return false;
            }
            LOCK(cs_main);
            BlockMap::iterator mi = mapBlockIndex.find(nHashOutpointConfirmed);
            if(mi == mapBlockIndex.end()) {
                // not on this chain?
                LogPrint("instantsend", "txLockRequest::IsValid -- Failed to find block %s for outpoint %s\n", nHashOutpointConfirmed.ToString(), txin.prevout.ToStringShort());
                return false;
            }
            nPrevoutHeight = mi->second ? mi->second->nHeight : 0;
        }

        int nTxAge = chainActive.Height() - (nPrevoutHeight ? nPrevoutHeight : coins.nHeight) + 1;
        // 1 less than the "send IS" gui requires, in case of a block propagating the network at the time
        int nConfirmationsRequired = INSTANTSEND_CONFIRMATIONS_REQUIRED - 1;

        if(nTxAge < nConfirmationsRequired) {
            LogPrint("instantsend", "CTxLockRequest::IsValid -- outpoint %s too new: nTxAge=%d, nConfirmationsRequired=%d, txid=%s\n",
                    txin.prevout.ToStringShort(), nTxAge, nConfirmationsRequired, GetHash().ToString());
            return false;
        }

        nValueIn += coins.vout[txin.prevout.n].nValue;
    }

    if(nValueOut > sporkManager.GetSporkValue(SPORK_5_INSTANTSEND_MAX_VALUE)*COIN) {
        LogPrint("instantsend", "CTxLockRequest::IsValid -- Transaction value too high: nValueOut=%d, tx=%s", nValueOut, ToString());
        return false;
    }

    if(nValueIn - nValueOut < GetMinFee()) {
        LogPrint("instantsend", "CTxLockRequest::IsValid -- did not include enough fees in transaction: fees=%d, tx=%s", nValueOut - nValueIn, ToString());
        return false;
    }

    return true;
}

CAmount CTxLockRequest::GetMinFee() const
{
    CAmount nMinFee = MIN_FEE;
    return std::max(nMinFee, CAmount(vin.size() * nMinFee));
}

int CTxLockRequest::GetMaxSignatures() const
{
    return vin.size() * COutPointLock::SIGNATURES_TOTAL;
}

bool CTxLockRequest::IsTimedOut() const
{
    return GetTime() - nTimeCreated > TIMEOUT_SECONDS;
}

//
// CTxLockVote
//

bool CTxLockVote::IsValid(CNode* pnode) const
{
    if(!snodeman.Has(CTxIn(outpointStormnode))) {
        LogPrint("instantsend", "CTxLockVote::IsValid -- Unknown stormnode %s\n", outpointStormnode.ToStringShort());
        snodeman.AskForSN(pnode, CTxIn(outpointStormnode));
        return false;
    }

    int nPrevoutHeight = GetUTXOHeight(outpoint);
    if(nPrevoutHeight == -1) {
        LogPrint("instantsend", "CTxLockVote::IsValid -- Failed to find UTXO %s\n", outpoint.ToStringShort());
        // Validating utxo set is not enough, votes can arrive after outpoint was already spent,
        // if lock request was mined. We should process them too to count them later if they are legit.
        CTransaction txOutpointCreated;
        uint256 nHashOutpointConfirmed;
        if(!GetTransaction(outpoint.hash, txOutpointCreated, Params().GetConsensus(), nHashOutpointConfirmed, true) || nHashOutpointConfirmed == uint256()) {
            LogPrint("instantsend", "CTxLockVote::IsValid -- Failed to find outpoint %s\n", outpoint.ToStringShort());
            return false;
        }
        LOCK(cs_main);
        BlockMap::iterator mi = mapBlockIndex.find(nHashOutpointConfirmed);
        if(mi == mapBlockIndex.end() || !mi->second) {
            // not on this chain?
            LogPrint("instantsend", "CTxLockVote::IsValid -- Failed to find block %s for outpoint %s\n", nHashOutpointConfirmed.ToString(), outpoint.ToStringShort());
            return false;
        }
        nPrevoutHeight = mi->second->nHeight;
    }

    int nLockInputHeight = nPrevoutHeight + 4;

    int n = snodeman.GetStormnodeRank(CTxIn(outpointStormnode), nLockInputHeight, MIN_INSTANTSEND_PROTO_VERSION);

    if(n == -1) {
        //can be caused by past versions trying to vote with an invalid protocol
        LogPrint("instantsend", "CTxLockVote::IsValid -- Outdated stormnode %s\n", outpointStormnode.ToStringShort());
        return false;
    }
    LogPrint("instantsend", "CTxLockVote::IsValid -- Stormnode %s, rank=%d\n", outpointStormnode.ToStringShort(), n);

    int nSignaturesTotal = COutPointLock::SIGNATURES_TOTAL;
    if(n > nSignaturesTotal) {
        LogPrint("instantsend", "CTxLockVote::IsValid -- Stormnode %s is not in the top %d (%d), vote hash=%s\n",
                outpointStormnode.ToStringShort(), nSignaturesTotal, n, GetHash().ToString());
        return false;
    }

    if(!CheckSignature()) {
        LogPrintf("CTxLockVote::IsValid -- Signature invalid\n");
        return false;
    }

    return true;
}

uint256 CTxLockVote::GetHash() const
{
    CHashWriter ss(SER_GETHASH, PROTOCOL_VERSION);
    ss << txHash;
    ss << outpoint;
    ss << outpointStormnode;
    return ss.GetHash();
}

bool CTxLockVote::CheckSignature() const
{
    std::string strError;
    std::string strMessage = txHash.ToString() + outpoint.ToStringShort();

    stormnode_info_t infoSn = snodeman.GetStormnodeInfo(CTxIn(outpointStormnode));

    if(!infoSn.fInfoValid) {
        LogPrintf("CTxLockVote::CheckSignature -- Unknown Stormnode: stormnode=%s\n", outpointStormnode.ToString());
        return false;
    }

    if(!privateSendSigner.VerifyMessage(infoSn.pubKeyStormnode, vchStormnodeSignature, strMessage, strError)) {
        LogPrintf("CTxLockVote::CheckSignature -- VerifyMessage() failed, error: %s\n", strError);
        return false;
    }

    return true;
}

bool CTxLockVote::Sign()
{
    std::string strError;
    std::string strMessage = txHash.ToString() + outpoint.ToStringShort();

    if(!privateSendSigner.SignMessage(strMessage, vchStormnodeSignature, activeStormnode.keyStormnode)) {
        LogPrintf("CTxLockVote::Sign -- SignMessage() failed\n");
        return false;
    }

    if(!privateSendSigner.VerifyMessage(activeStormnode.pubKeyStormnode, vchStormnodeSignature, strMessage, strError)) {
        LogPrintf("CTxLockVote::Sign -- VerifyMessage() failed, error: %s\n", strError);
        return false;
    }

    return true;
}

void CTxLockVote::Relay() const
{
    CInv inv(MSG_TXLOCK_VOTE, GetHash());
    RelayInv(inv);
}

bool CTxLockVote::IsExpired(int nHeight) const
{
    // Locks and votes expire nInstantSendKeepLock blocks after the block corresponding tx was included into.
    return (nConfirmedHeight != -1) && (nHeight - nConfirmedHeight > Params().GetConsensus().nInstantSendKeepLock);
}

//
// COutPointLock
//

bool COutPointLock::AddVote(const CTxLockVote& vote)
{
    if(mapStormnodeVotes.count(vote.GetStormnodeOutpoint()))
        return false;

mapStormnodeVotes.insert(std::make_pair(vote.GetStormnodeOutpoint(), vote));
    return true;
}

std::vector<CTxLockVote> COutPointLock::GetVotes() const
{
    std::vector<CTxLockVote> vRet;
    std::map<COutPoint, CTxLockVote>::const_iterator itVote = mapStormnodeVotes.begin();
    while(itVote != mapStormnodeVotes.end()) {
        vRet.push_back(itVote->second);
        ++itVote;
    }
    return vRet;
}

bool COutPointLock::HasStormnodeVoted(const COutPoint& outpointStormnodeIn) const
{
    return mapStormnodeVotes.count(outpointStormnodeIn);
}

void COutPointLock::Relay() const
{
    std::map<COutPoint, CTxLockVote>::const_iterator itVote = mapStormnodeVotes.begin();
    while(itVote != mapStormnodeVotes.end()) {
        itVote->second.Relay();
        ++itVote;
    }
}

//
// CTxLockCandidate
//
void CTxLockCandidate::AddOutPointLock(const COutPoint& outpoint)
{
    mapOutPointLocks.insert(make_pair(outpoint, COutPointLock(outpoint)));
}

bool CTxLockCandidate::AddVote(const CTxLockVote& vote)
{
    std::map<COutPoint, COutPointLock>::iterator it = mapOutPointLocks.find(vote.GetOutpoint());
    if(it == mapOutPointLocks.end()) return false;
    return it->second.AddVote(vote);
}

bool CTxLockCandidate::IsAllOutPointsReady() const
{
    if(mapOutPointLocks.empty()) return false;

    std::map<COutPoint, COutPointLock>::const_iterator it = mapOutPointLocks.begin();
    while(it != mapOutPointLocks.end()) {
        if(!it->second.IsReady()) return false;
        ++it;
    }
    return true;
}

bool CTxLockCandidate::HasStormnodeVoted(const COutPoint& outpointIn, const COutPoint& outpointStormnodeIn)
{
    std::map<COutPoint, COutPointLock>::iterator it = mapOutPointLocks.find(outpointIn);
    return it !=mapOutPointLocks.end() && it->second.HasStormnodeVoted(outpointStormnodeIn);
}

int CTxLockCandidate::CountVotes() const
{
    // Note: do NOT use vote count to figure out if tx is locked, use IsAllOutPointsReady() instead
    int nCountVotes = 0;
    std::map<COutPoint, COutPointLock>::const_iterator it = mapOutPointLocks.begin();
    while(it != mapOutPointLocks.end()) {
        nCountVotes += it->second.CountVotes();
        ++it;
    }
    return nCountVotes;
}

bool CTxLockCandidate::IsExpired(int nHeight) const
{
    // Locks and votes expire nInstantSendKeepLock blocks after the block corresponding tx was included into.
    return (nConfirmedHeight != -1) && (nHeight - nConfirmedHeight > Params().GetConsensus().nInstantSendKeepLock);
}

void CTxLockCandidate::Relay() const
{
    RelayTransaction(txLockRequest);
    std::map<COutPoint, COutPointLock>::const_iterator itOutpointLock = mapOutPointLocks.begin();
    while(itOutpointLock != mapOutPointLocks.end()) {
        itOutpointLock->second.Relay();
        ++itOutpointLock;
    }
}
