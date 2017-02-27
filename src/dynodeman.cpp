// Copyright (c) 2014-2017 The Dash Core Developers
// Copyright (c) 2015-2017 Duality Blockchain Solutions Developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "dynodeman.h"

#include "activedynode.h"
#include "addrman.h"
#include "governance.h"
#include "netfulfilledman.h"
#include "privatesend.h"
#include "dynode-payments.h"
#include "dynode-sync.h"
#include "util.h"

/** Dynode manager */
CDynodeMan snodeman;

const std::string CDynodeMan::SERIALIZATION_VERSION_STRING = "CDynodeMan-Version-1";

struct CompareLastPaidBlock
{
    bool operator()(const std::pair<int, CDynode*>& t1,
                    const std::pair<int, CDynode*>& t2) const
    {
        return (t1.first != t2.first) ? (t1.first < t2.first) : (t1.second->vin < t2.second->vin);
    }
};

struct CompareScoreSN
{
    bool operator()(const std::pair<int64_t, CDynode*>& t1,
                    const std::pair<int64_t, CDynode*>& t2) const
    {
        return (t1.first != t2.first) ? (t1.first < t2.first) : (t1.second->vin < t2.second->vin);
    }
};

CDynodeIndex::CDynodeIndex()
    : nSize(0),
      mapIndex(),
      mapReverseIndex()
{}

bool CDynodeIndex::Get(int nIndex, CTxIn& vinDynode) const
{
    rindex_m_cit it = mapReverseIndex.find(nIndex);
    if(it == mapReverseIndex.end()) {
        return false;
    }
    vinDynode = it->second;
    return true;
}

int CDynodeIndex::GetDynodeIndex(const CTxIn& vinDynode) const
{
    index_m_cit it = mapIndex.find(vinDynode);
    if(it == mapIndex.end()) {
        return -1;
    }
    return it->second;
}

void CDynodeIndex::AddDynodeVIN(const CTxIn& vinDynode)
{
    index_m_it it = mapIndex.find(vinDynode);
    if(it != mapIndex.end()) {
        return;
    }
    int nNextIndex = nSize;
    mapIndex[vinDynode] = nNextIndex;
    mapReverseIndex[nNextIndex] = vinDynode;
    ++nSize;
}

void CDynodeIndex::Clear()
{
    mapIndex.clear();
    mapReverseIndex.clear();
    nSize = 0;
}
struct CompareByAddr

{
    bool operator()(const CDynode* t1,
                    const CDynode* t2) const
    {
        return t1->addr < t2->addr;
    }
};

void CDynodeIndex::RebuildIndex()
{
    nSize = mapIndex.size();
    for(index_m_it it = mapIndex.begin(); it != mapIndex.end(); ++it) {
        mapReverseIndex[it->second] = it->first;
    }
}

CDynodeMan::CDynodeMan()
: cs(),
  vDynodes(),
  mAskedUsForDynodeList(),
  mWeAskedForDynodeList(),
  mWeAskedForDynodeListEntry(),
  mWeAskedForVerification(),
  mSnbRecoveryRequests(),
  mSnbRecoveryGoodReplies(),
  listScheduledSnbRequestConnections(),
  nLastIndexRebuildTime(0),
  indexDynodes(),
  indexDynodesOld(),
  fIndexRebuilt(false),
  fDynodesAdded(false),
  fDynodesRemoved(false),
  vecDirtyGovernanceObjectHashes(),
  nLastWatchdogVoteTime(0),
  mapSeenDynodeBroadcast(),
  mapSeenDynodePing(),
  nSsqCount(0)
{}

bool CDynodeMan::Add(CDynode &sn)
{
    LOCK(cs);

    CDynode *psn = Find(sn.vin);
    if (psn == NULL) {
        LogPrint("Dynode", "CDynodeMan::Add -- Adding new Dynode: addr=%s, %i now\n", sn.addr.ToString(), size() + 1);
        sn.nTimeLastWatchdogVote = sn.sigTime;
        vDynodes.push_back(sn);
        indexDynodes.AddDynodeVIN(sn.vin);
        fDynodesAdded = true;
        return true;
    }

    return false;
}

void CDynodeMan::AskForSN(CNode* pnode, const CTxIn &vin)
{
    if(!pnode) return;

    std::map<COutPoint, std::map<CNetAddr, int64_t> >::iterator it1 = mWeAskedForDynodeListEntry.find(vin.prevout);
    if (it1 != mWeAskedForDynodeListEntry.end()) {
        std::map<CNetAddr, int64_t>::iterator it2 = it1->second.find(pnode->addr);
        if (it2 != it1->second.end()) {
            if (GetTime() < it2->second) {
                // we've asked recently, should not repeat too often or we could get banned
                return;
            }
            // we asked this node for this outpoint but it's ok to ask again already
            LogPrintf("CDynodeMan::AskForSN -- Asking same peer %s for missing Dynode entry again: %s\n", pnode->addr.ToString(), vin.prevout.ToStringShort());
        } else {
            // we already asked for this outpoint but not this node
            LogPrintf("CDynodeMan::AskForSN -- Asking new peer %s for missing Dynode entry: %s\n", pnode->addr.ToString(), vin.prevout.ToStringShort());
        }
    } else {
        // we never asked any node for this outpoint
        LogPrintf("CDynodeMan::AskForSN -- Asking peer %s for missing Dynode entry for the first time: %s\n", pnode->addr.ToString(), vin.prevout.ToStringShort());
    }
    mWeAskedForDynodeListEntry[vin.prevout][pnode->addr] = GetTime() + SSEG_UPDATE_SECONDS;

    pnode->PushMessage(NetMsgType::SSEG, vin);
}

void CDynodeMan::Check()
{
    LOCK(cs);

    LogPrint("Dynode", "CDynodeMan::Check -- nLastWatchdogVoteTime=%d, IsWatchdogActive()=%d\n", nLastWatchdogVoteTime, IsWatchdogActive());

    BOOST_FOREACH(CDynode& sn, vDynodes) {
        sn.Check();
    }
}

void CDynodeMan::CheckAndRemove()
{
    if(!dynodeSync.IsDynodeListSynced()) return;

    LogPrintf("CDynodeMan::CheckAndRemove\n");

    {
        // Need LOCK2 here to ensure consistent locking order because code below locks cs_main
        // in CheckSnbAndUpdateDynodeList()
        LOCK2(cs_main, cs);

        Check();

        // Remove spent Dynodes, prepare structures and make requests to reasure the state of inactive ones
        std::vector<CDynode>::iterator it = vDynodes.begin();
        std::vector<std::pair<int, CDynode> > vecDynodeRanks;
        // ask for up to SNB_RECOVERY_MAX_ASK_ENTRIES dynode entries at a time
        int nAskForSnbRecovery = SNB_RECOVERY_MAX_ASK_ENTRIES;
        while(it != vDynodes.end()) {
            CDynodeBroadcast snb = CDynodeBroadcast(*it);
            uint256 hash = snb.GetHash();
            // If collateral was spent ...
            if ((*it).IsOutpointSpent()) {
                LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- Removing Dynode: %s  addr=%s  %i now\n", (*it).GetStateString(), (*it).addr.ToString(), size() - 1);
                // erase all of the broadcasts we've seen from this txin, ...
                mapSeenDynodeBroadcast.erase(hash);
                mWeAskedForDynodeListEntry.erase((*it).vin.prevout);
                // and finally remove it from the list
                it->FlagGovernanceItemsAsDirty();
                it = vDynodes.erase(it);
                fDynodesRemoved = true;
            } else {
                bool fAsk = pCurrentBlockIndex &&
                            (nAskForSnbRecovery > 0) &&
                            dynodeSync.IsSynced() &&
                            it->IsNewStartRequired() &&
                            !IsSnbRecoveryRequested(hash);
                if(fAsk) {
                    // this sn is in a non-recoverable state and we haven't asked other nodes yet
                    std::set<CNetAddr> setRequested;
                    // calulate only once and only when it's needed
                    if(vecDynodeRanks.empty()) {
                        int nRandomBlockHeight = GetRandInt(pCurrentBlockIndex->nHeight);
                        vecDynodeRanks = GetDynodeRanks(nRandomBlockHeight);
                    }
                    bool fAskedForSnbRecovery = false;
                    // ask first SNB_RECOVERY_QUORUM_TOTAL dynodes we can connect to and we haven't asked recently
                    for(int i = 0; setRequested.size() < SNB_RECOVERY_QUORUM_TOTAL && i < (int)vecDynodeRanks.size(); i++) {
                        // avoid banning
                        if(mWeAskedForDynodeListEntry.count(it->vin.prevout) && mWeAskedForDynodeListEntry[it->vin.prevout].count(vecDynodeRanks[i].second.addr)) continue;
                        // didn't ask recently, ok to ask now
                        CService addr = vecDynodeRanks[i].second.addr;
                        setRequested.insert(addr);
                        listScheduledSnbRequestConnections.push_back(std::make_pair(addr, hash));
                        fAskedForSnbRecovery = true;
                    }
                    if(fAskedForSnbRecovery) {
                        LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- Recovery initiated, Dynode=%s\n", it->vin.prevout.ToStringShort());
                        nAskForSnbRecovery--;
                    }
                    // wait for snb recovery replies for SNB_RECOVERY_WAIT_SECONDS seconds
                    mSnbRecoveryRequests[hash] = std::make_pair(GetTime() + SNB_RECOVERY_WAIT_SECONDS, setRequested);
                }
                ++it;
            }
        }
        // proces replies for DYNODE_NEW_START_REQUIRED Dynodes
        LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- mSnbRecoveryGoodReplies size=%d\n", (int)mSnbRecoveryGoodReplies.size());
        std::map<uint256, std::vector<CDynodeBroadcast> >::iterator itSnbReplies = mSnbRecoveryGoodReplies.begin();
        while(itSnbReplies != mSnbRecoveryGoodReplies.end()){
            if(mSnbRecoveryRequests[itSnbReplies->first].first < GetTime()) {
                // all nodes we asked should have replied now
                if(itSnbReplies->second.size() >= SNB_RECOVERY_QUORUM_REQUIRED) {
                    // majority of nodes we asked agrees that this sn doesn't require new snb, reprocess one of new snbs
                    LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- reprocessing snb, Dynode=%s\n", itSnbReplies->second[0].vin.prevout.ToStringShort());
                    // mapSeenDynodeBroadcast.erase(itSnbReplies->first);
                    int nDos;
                    itSnbReplies->second[0].fRecovery = true;
                    CheckSnbAndUpdateDynodeList(NULL, itSnbReplies->second[0], nDos);
                }
                LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- removing snb recovery reply, Dynode=%s, size=%d\n", itSnbReplies->second[0].vin.prevout.ToStringShort(), (int)itSnbReplies->second.size());
                mSnbRecoveryGoodReplies.erase(itSnbReplies++);
            } else {
                ++itSnbReplies;
            }
        }
    }
    {
        // no need for cm_main below
        LOCK(cs);

        std::map<uint256, std::pair< int64_t, std::set<CNetAddr> > >::iterator itSnbRequest = mSnbRecoveryRequests.begin();
        while(itSnbRequest != mSnbRecoveryRequests.end()){
            // Allow this snb to be re-verified again after SNB_RECOVERY_RETRY_SECONDS seconds
            // if sn is still in DYNODE_NEW_START_REQUIRED state.
            if(GetTime() - itSnbRequest->second.first > SNB_RECOVERY_RETRY_SECONDS) {
                mSnbRecoveryRequests.erase(itSnbRequest++);
            } else {
                ++itSnbRequest;
            }
        }

        // check who's asked for the Dynode list
        std::map<CNetAddr, int64_t>::iterator it1 = mAskedUsForDynodeList.begin();
        while(it1 != mAskedUsForDynodeList.end()){
            if((*it1).second < GetTime()) {
                mAskedUsForDynodeList.erase(it1++);
            } else {
                ++it1;
            }
        }

        // check who we asked for the Dynode list
        it1 = mWeAskedForDynodeList.begin();
        while(it1 != mWeAskedForDynodeList.end()){
            if((*it1).second < GetTime()){
                mWeAskedForDynodeList.erase(it1++);
            } else {
                ++it1;
            }
        }

        // check which Dynodes we've asked for
        std::map<COutPoint, std::map<CNetAddr, int64_t> >::iterator it2 = mWeAskedForDynodeListEntry.begin();
        while(it2 != mWeAskedForDynodeListEntry.end()){
            std::map<CNetAddr, int64_t>::iterator it3 = it2->second.begin();
            while(it3 != it2->second.end()){
                if(it3->second < GetTime()){
                    it2->second.erase(it3++);
                } else {
                    ++it3;
                }
            }
            if(it2->second.empty()) {
                mWeAskedForDynodeListEntry.erase(it2++);
            } else {
                ++it2;
            }
        }

        std::map<CNetAddr, CDynodeVerification>::iterator it3 = mWeAskedForVerification.begin();
        while(it3 != mWeAskedForVerification.end()){
            if(it3->second.nBlockHeight < pCurrentBlockIndex->nHeight - MAX_POSE_BLOCKS) {
                mWeAskedForVerification.erase(it3++);
            } else {
                ++it3;
            }
        }

        // NOTE: do not expire mapSeenDynodeBroadcast entries here, clean them on snb updates!

        // remove expired mapSeenDynodePing
        std::map<uint256, CDynodePing>::iterator it4 = mapSeenDynodePing.begin();
        while(it4 != mapSeenDynodePing.end()){
            if((*it4).second.IsExpired()) {
                LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- Removing expired Dynode ping: hash=%s\n", (*it4).second.GetHash().ToString());
                mapSeenDynodePing.erase(it4++);
            } else {
                ++it4;
            }
        }

        // remove expired mapSeenDynodeVerification
        std::map<uint256, CDynodeVerification>::iterator itv2 = mapSeenDynodeVerification.begin();
        while(itv2 != mapSeenDynodeVerification.end()){
            if((*itv2).second.nBlockHeight < pCurrentBlockIndex->nHeight - MAX_POSE_BLOCKS){
                LogPrint("Dynode", "CDynodeMan::CheckAndRemove -- Removing expired Dynode verification: hash=%s\n", (*itv2).first.ToString());
                mapSeenDynodeVerification.erase(itv2++);
            } else {
                ++itv2;
            }
        }

        LogPrintf("CDynodeMan::CheckAndRemove -- %s\n", ToString());

        if(fDynodesRemoved) {
            CheckAndRebuildDynodeIndex();
        }
    }

    if(fDynodesRemoved) {
        NotifyDynodeUpdates();
    }
}

void CDynodeMan::Clear()
{
    LOCK(cs);
    vDynodes.clear();
    mAskedUsForDynodeList.clear();
    mWeAskedForDynodeList.clear();
    mWeAskedForDynodeListEntry.clear();
    mapSeenDynodeBroadcast.clear();
    mapSeenDynodePing.clear();
    nSsqCount = 0;
    nLastWatchdogVoteTime = 0;
    indexDynodes.Clear();
    indexDynodesOld.Clear();
}

int CDynodeMan::CountDynodes(int nProtocolVersion)
{
    LOCK(cs);
    int nCount = 0;
    nProtocolVersion = nProtocolVersion == -1 ? snpayments.GetMinDynodePaymentsProto() : nProtocolVersion;

    BOOST_FOREACH(CDynode& sn, vDynodes) {
        if(sn.nProtocolVersion < nProtocolVersion) continue;
        nCount++;
    }

    return nCount;
}

int CDynodeMan::CountEnabled(int nProtocolVersion)
{
    LOCK(cs);
    int nCount = 0;
    nProtocolVersion = nProtocolVersion == -1 ? snpayments.GetMinDynodePaymentsProto() : nProtocolVersion;

    BOOST_FOREACH(CDynode& sn, vDynodes) {
        if(sn.nProtocolVersion < nProtocolVersion || !sn.IsEnabled()) continue;
        nCount++;
    }

    return nCount;
}

/* Only IPv4 Dynodes are allowed, saving this for later
int CDynodeMan::CountByIP(int nNetworkType)
{
    LOCK(cs);
    int nNodeCount = 0;

    BOOST_FOREACH(CDynode& sn, vDynodes)
        if ((nNetworkType == NET_IPV4 && sn.addr.IsIPv4()) ||
            (nNetworkType == NET_TOR  && sn.addr.IsTor())  ||
            (nNetworkType == NET_IPV6 && sn.addr.IsIPv6())) {
                nNodeCount++;
        }

    return nNodeCount;
}
*/

void CDynodeMan::SsegUpdate(CNode* pnode)
{
    LOCK(cs);
    
    if(Params().NetworkIDString() == CBaseChainParams::MAIN) {     
        if(!(pnode->addr.IsRFC1918() || pnode->addr.IsLocal())) {
            std::map<CNetAddr, int64_t>::iterator it = mWeAskedForDynodeList.find(pnode->addr);
            if(it != mWeAskedForDynodeList.end() && GetTime() < (*it).second) {
                LogPrintf("CDynodeMan::SsegUpdate -- we already asked %s for the list; skipping...\n", pnode->addr.ToString());
                return;
            }
        }
    }      

    pnode->PushMessage(NetMsgType::SSEG, CTxIn());
    int64_t askAgain = GetTime() + SSEG_UPDATE_SECONDS;
    mWeAskedForDynodeList[pnode->addr] = askAgain;

    LogPrint("Dynode", "CDynodeMan::SsegUpdate -- asked %s for the list\n", pnode->addr.ToString());
}

CDynode* CDynodeMan::Find(const CScript &payee)
{
    LOCK(cs);

    BOOST_FOREACH(CDynode& sn, vDynodes)
    {
        if(GetScriptForDestination(sn.pubKeyCollateralAddress.GetID()) == payee)
            return &sn;
    }
    return NULL;
}

CDynode* CDynodeMan::Find(const CTxIn &vin)
{
    LOCK(cs);

    BOOST_FOREACH(CDynode& sn, vDynodes)
    {
        if(sn.vin.prevout == vin.prevout)
            return &sn;
    }
    return NULL;
}

CDynode* CDynodeMan::Find(const CPubKey &pubKeyDynode)
{
    LOCK(cs);

    BOOST_FOREACH(CDynode& sn, vDynodes)
    {
        if(sn.pubKeyDynode == pubKeyDynode)
            return &sn;
    }
    return NULL;
}

bool CDynodeMan::Get(const CPubKey& pubKeyDynode, CDynode& dynode)
{
    // Theses mutexes are recursive so double locking by the same thread is safe.
    LOCK(cs);
    CDynode* pSN = Find(pubKeyDynode);
    if(!pSN)  {
        return false;
    }
    dynode = *pSN;
    return true;
}

bool CDynodeMan::Get(const CTxIn& vin, CDynode& dynode)
{
    // Theses mutexes are recursive so double locking by the same thread is safe.
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return false;
    }
    dynode = *pSN;
    return true;
}

dynode_info_t CDynodeMan::GetDynodeInfo(const CTxIn& vin)
{
    dynode_info_t info;
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return info;
    }
    info = pSN->GetInfo();
    return info;
}

dynode_info_t CDynodeMan::GetDynodeInfo(const CPubKey& pubKeyDynode)
{
    dynode_info_t info;
    LOCK(cs);
    CDynode* pSN = Find(pubKeyDynode);
    if(!pSN)  {
        return info;
    }
    info = pSN->GetInfo();
    return info;
}

bool CDynodeMan::Has(const CTxIn& vin)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    return (pSN != NULL);
}

//
// Deterministically select the oldest/best Dynode to pay on the network
//
CDynode* CDynodeMan::GetNextDynodeInQueueForPayment(bool fFilterSigTime, int& nCount)
{
    if(!pCurrentBlockIndex) {
        nCount = 0;
        return NULL;
    }
    return GetNextDynodeInQueueForPayment(pCurrentBlockIndex->nHeight, fFilterSigTime, nCount);
}

CDynode* CDynodeMan::GetNextDynodeInQueueForPayment(int nBlockHeight, bool fFilterSigTime, int& nCount)
{
    // Need LOCK2 here to ensure consistent locking order because the GetBlockHash call below locks cs_main
    LOCK2(cs_main,cs);

    CDynode *pBestDynode = NULL;
    std::vector<std::pair<int, CDynode*> > vecDynodeLastPaid;

    /*
        Make a vector with all of the last paid times
    */

    int nSnCount = CountEnabled();
    BOOST_FOREACH(CDynode &sn, vDynodes)
    {
        if(!sn.IsValidForPayment()) continue;

        // //check protocol version
        if(sn.nProtocolVersion < snpayments.GetMinDynodePaymentsProto()) continue;

        //it's in the list (up to 8 entries ahead of current block to allow propagation) -- so let's skip it
        if(snpayments.IsScheduled(sn, nBlockHeight)) continue;

        //it's too new, wait for a cycle
        if(fFilterSigTime && sn.sigTime + (nSnCount*2.6*60) > GetAdjustedTime()) continue;

        //make sure it has at least as many confirmations as there are Dynodes
        if(sn.GetCollateralAge() < nSnCount) continue;

        vecDynodeLastPaid.push_back(std::make_pair(sn.GetLastPaidBlock(), &sn));
    }

    nCount = (int)vecDynodeLastPaid.size();

    //when the network is in the process of upgrading, don't penalize nodes that recently restarted
    if(fFilterSigTime && nCount < nSnCount/3) return GetNextDynodeInQueueForPayment(nBlockHeight, false, nCount);

    // Sort them low to high
    sort(vecDynodeLastPaid.begin(), vecDynodeLastPaid.end(), CompareLastPaidBlock());

    uint256 blockHash;
    if(!GetBlockHash(blockHash, nBlockHeight - 101)) {
        LogPrintf("CDynode::GetNextDynodeInQueueForPayment -- ERROR: GetBlockHash() failed at nBlockHeight %d\n", nBlockHeight - 101);
        return NULL;
    }
    // Look at 1/10 of the oldest nodes (by last payment), calculate their scores and pay the best one
    //  -- This doesn't look at who is being paid in the +8-10 blocks, allowing for double payments very rarely
    //  -- 1/100 payments should be a double payment on mainnet - (1/(3000/10))*2
    //  -- (chance per block * chances before IsScheduled will fire)
    int nTenthNetwork = nSnCount/10;
    int nCountTenth = 0;
    arith_uint256 nHighest = 0;
    BOOST_FOREACH (PAIRTYPE(int, CDynode*)& s, vecDynodeLastPaid){
        arith_uint256 nScore = s.second->CalculateScore(blockHash);
        if(nScore > nHighest){
            nHighest = nScore;
            pBestDynode = s.second;
        }
        nCountTenth++;
        if(nCountTenth >= nTenthNetwork) break;
    }
    return pBestDynode;
}

CDynode* CDynodeMan::FindRandomNotInVec(const std::vector<CTxIn> &vecToExclude, int nProtocolVersion)
{
    LOCK(cs);

    nProtocolVersion = nProtocolVersion == -1 ? snpayments.GetMinDynodePaymentsProto() : nProtocolVersion;

    int nCountEnabled = CountEnabled(nProtocolVersion);
    int nCountNotExcluded = nCountEnabled - vecToExclude.size();

    LogPrintf("CDynodeMan::FindRandomNotInVec -- %d enabled Dynodes, %d Dynodes to choose from\n", nCountEnabled, nCountNotExcluded);
    if(nCountNotExcluded < 1) return NULL;

    // fill a vector of pointers
    std::vector<CDynode*> vpDynodesShuffled;
    BOOST_FOREACH(CDynode &sn, vDynodes) {
        vpDynodesShuffled.push_back(&sn);
    }

    InsecureRand insecureRand;

    // shuffle pointers
    std::random_shuffle(vpDynodesShuffled.begin(), vpDynodesShuffled.end(), insecureRand);
    bool fExclude;

    // loop through
    BOOST_FOREACH(CDynode* psn, vpDynodesShuffled) {
        if(psn->nProtocolVersion < nProtocolVersion || !psn->IsEnabled()) continue;
        fExclude = false;
        BOOST_FOREACH(const CTxIn &txinToExclude, vecToExclude) {
            if(psn->vin.prevout == txinToExclude.prevout) {
                fExclude = true;
                break;
            }
        }
        if(fExclude) continue;
        // found the one not in vecToExclude
        LogPrint("Dynode", "CDynodeMan::FindRandomNotInVec -- found, Dynode=%s\n", psn->vin.prevout.ToStringShort());
        return psn;
    }

    LogPrint("Dynode", "CDynodeMan::FindRandomNotInVec -- failed\n");
    return NULL;
}

int CDynodeMan::GetDynodeRank(const CTxIn& vin, int nBlockHeight, int nMinProtocol, bool fOnlyActive)
{
    std::vector<std::pair<int64_t, CDynode*> > vecDynodeScores;

    //make sure we know about this block
    uint256 blockHash = uint256();
    if(!GetBlockHash(blockHash, nBlockHeight)) return -1;

    LOCK(cs);

    // scan for winner
    BOOST_FOREACH(CDynode& sn, vDynodes) {
        if(sn.nProtocolVersion < nMinProtocol) continue;
        if(fOnlyActive) {
            if(!sn.IsEnabled()) continue;
        }
        else {
            if(!sn.IsValidForPayment()) continue;
        }
        int64_t nScore = sn.CalculateScore(blockHash).GetCompact(false);

        vecDynodeScores.push_back(std::make_pair(nScore, &sn));
    }

    sort(vecDynodeScores.rbegin(), vecDynodeScores.rend(), CompareScoreSN());

    int nRank = 0;
    BOOST_FOREACH (PAIRTYPE(int64_t, CDynode*)& scorePair, vecDynodeScores) {
        nRank++;
        if(scorePair.second->vin.prevout == vin.prevout) return nRank;
    }

    return -1;
}

std::vector<std::pair<int, CDynode> > CDynodeMan::GetDynodeRanks(int nBlockHeight, int nMinProtocol)
{
    std::vector<std::pair<int64_t, CDynode*> > vecDynodeScores;
    std::vector<std::pair<int, CDynode> > vecDynodeRanks;

    //make sure we know about this block
    uint256 blockHash = uint256();
    if(!GetBlockHash(blockHash, nBlockHeight)) return vecDynodeRanks;

    LOCK(cs);

    // scan for winner
    BOOST_FOREACH(CDynode& sn, vDynodes) {

        if(sn.nProtocolVersion < nMinProtocol || !sn.IsEnabled()) continue;

        int64_t nScore = sn.CalculateScore(blockHash).GetCompact(false);

        vecDynodeScores.push_back(std::make_pair(nScore, &sn));
    }

    sort(vecDynodeScores.rbegin(), vecDynodeScores.rend(), CompareScoreSN());

    int nRank = 0;
    BOOST_FOREACH (PAIRTYPE(int64_t, CDynode*)& s, vecDynodeScores) {
        nRank++;
        vecDynodeRanks.push_back(std::make_pair(nRank, *s.second));
    }

    return vecDynodeRanks;
}

CDynode* CDynodeMan::GetDynodeByRank(int nRank, int nBlockHeight, int nMinProtocol, bool fOnlyActive)
{
    std::vector<std::pair<int64_t, CDynode*> > vecDynodeScores;

    LOCK(cs);

    uint256 blockHash;
    if(!GetBlockHash(blockHash, nBlockHeight)) {
        LogPrintf("CDynode::GetDynodeByRank -- ERROR: GetBlockHash() failed at nBlockHeight %d\n", nBlockHeight);
        return NULL;
    }

    // Fill scores
    BOOST_FOREACH(CDynode& sn, vDynodes) {

        if(sn.nProtocolVersion < nMinProtocol) continue;
        if(fOnlyActive && !sn.IsEnabled()) continue;

        int64_t nScore = sn.CalculateScore(blockHash).GetCompact(false);

        vecDynodeScores.push_back(std::make_pair(nScore, &sn));
    }

    sort(vecDynodeScores.rbegin(), vecDynodeScores.rend(), CompareScoreSN());

    int rank = 0;
    BOOST_FOREACH (PAIRTYPE(int64_t, CDynode*)& s, vecDynodeScores){
        rank++;
        if(rank == nRank) {
            return s.second;
        }
    }

    return NULL;
}

void CDynodeMan::ProcessDynodeConnections()
{
    //we don't care about this for regtest
    if(Params().NetworkIDString() == CBaseChainParams::REGTEST) return;

    LOCK(cs_vNodes);
    BOOST_FOREACH(CNode* pnode, vNodes) {
        if(pnode->fDynode) {
            if(privateSendPool.pSubmittedToDynode != NULL && pnode->addr == privateSendPool.pSubmittedToDynode->addr) continue;
            LogPrintf("Closing Dynode connection: peer=%d, addr=%s\n", pnode->id, pnode->addr.ToString());
            pnode->fDisconnect = true;
        }
    }
}

std::pair<CService, std::set<uint256> > CDynodeMan::PopScheduledSnbRequestConnection()
{
    LOCK(cs);
    if(listScheduledSnbRequestConnections.empty()) {
        return std::make_pair(CService(), std::set<uint256>());
    }

    std::set<uint256> setResult;

    listScheduledSnbRequestConnections.sort();
    std::pair<CService, uint256> pairFront = listScheduledSnbRequestConnections.front();

    // squash hashes from requests with the same CService as the first one into setResult
    std::list< std::pair<CService, uint256> >::iterator it = listScheduledSnbRequestConnections.begin();
    while(it != listScheduledSnbRequestConnections.end()) {
        if(pairFront.first == it->first) {
            setResult.insert(it->second);
            it = listScheduledSnbRequestConnections.erase(it);
        } else {
            // since list is sorted now, we can be sure that there is no more hashes left
            // to ask for from this addr
            break;
        }
    }
    return std::make_pair(pairFront.first, setResult);
}

void CDynodeMan::ProcessMessage(CNode* pfrom, std::string& strCommand, CDataStream& vRecv)
{
    if(fLiteMode) return; // disable all Dynamic specific functionality
    if(!dynodeSync.IsBlockchainSynced()) return;

    if (strCommand == NetMsgType::SNANNOUNCE) { //Dynode Broadcast

        CDynodeBroadcast snb;
        vRecv >> snb;

        pfrom->setAskFor.erase(snb.GetHash());

        LogPrint("Dynode", "SNANNOUNCE -- Dynode announce, Dynode=%s\n", snb.vin.prevout.ToStringShort());

            int nDos = 0;

        if (CheckSnbAndUpdateDynodeList(pfrom, snb, nDos)) {
                // use announced Dynode as a peer
                addrman.Add(CAddress(snb.addr), pfrom->addr, 2*60*60);
            } else if(nDos > 0) {
                Misbehaving(pfrom->GetId(), nDos);
        }
        if(fDynodesAdded) {
            NotifyDynodeUpdates();
        }
    } else if (strCommand == NetMsgType::SNPING) { //Dynode Ping

        CDynodePing snp;
        vRecv >> snp;

        uint256 nHash = snp.GetHash();

        pfrom->setAskFor.erase(nHash);

        LogPrint("Dynode", "SNPING -- Dynode ping, Dynode=%s\n", snp.vin.prevout.ToStringShort());

        // Need LOCK2 here to ensure consistent locking order because the CheckAndUpdate call below locks cs_main
        LOCK2(cs_main, cs);

        if(mapSeenDynodePing.count(nHash)) return; //seen
        mapSeenDynodePing.insert(std::make_pair(nHash, snp));

        LogPrint("Dynode", "SNPING -- Dynode ping, Dynode=%s new\n", snp.vin.prevout.ToStringShort());

        // see if we have this Dynode
        CDynode* psn = snodeman.Find(snp.vin);

        // too late, new SNANNOUNCE is required
        if(psn && psn->IsNewStartRequired()) return;

        int nDos = 0;
        if(snp.CheckAndUpdate(psn, false, nDos)) return;

        if(nDos > 0) {
            // if anything significant failed, mark that node
            Misbehaving(pfrom->GetId(), nDos);
        } else if(psn != NULL) {
            // nothing significant failed, sn is a known one too
            return;
        }

        // something significant is broken or sn is unknown,
        // we might have to ask for a Dynode entry once
        AskForSN(pfrom, snp.vin);

    } else if (strCommand == NetMsgType::SSEG) { //Get Dynode list or specific entry
        // Ignore such requests until we are fully synced.
        // We could start processing this after Dynode list is synced
        // but this is a heavy one so it's better to finish sync first.
        if (!dynodeSync.IsSynced()) return;

        CTxIn vin;
        vRecv >> vin;

        LogPrint("Dynode", "SSEG -- Dynode list, Dynode=%s\n", vin.prevout.ToStringShort());

        LOCK(cs);

        if(vin == CTxIn()) { //only should ask for this once
            //local network
            bool isLocal = (pfrom->addr.IsRFC1918() || pfrom->addr.IsLocal());

            if(!isLocal && Params().NetworkIDString() == CBaseChainParams::MAIN) {
                std::map<CNetAddr, int64_t>::iterator i = mAskedUsForDynodeList.find(pfrom->addr);
                if (i != mAskedUsForDynodeList.end()){
                    int64_t t = (*i).second;
                    if (GetTime() < t) {
                        Misbehaving(pfrom->GetId(), 34);
                        LogPrintf("SSEG -- peer already asked me for the list, peer=%d\n", pfrom->id);
                        return;
                    }
                }
                int64_t askAgain = GetTime() + SSEG_UPDATE_SECONDS;
                mAskedUsForDynodeList[pfrom->addr] = askAgain;
            }
        } //else, asking for a specific node which is ok

        int nInvCount = 0;

        BOOST_FOREACH(CDynode& sn, vDynodes) {
            if (vin != CTxIn() && vin != sn.vin) continue; // asked for specific vin but we are not there yet
            if (sn.addr.IsRFC1918() || sn.addr.IsLocal()) continue; // do not send local network Dynode

            LogPrint("Dynode", "SSEG -- Sending Dynode entry: Dynode=%s  addr=%s\n", sn.vin.prevout.ToStringShort(), sn.addr.ToString());
            CDynodeBroadcast snb = CDynodeBroadcast(sn);
            uint256 hash = snb.GetHash();
            pfrom->PushInventory(CInv(MSG_DYNODE_ANNOUNCE, hash));
            pfrom->PushInventory(CInv(MSG_DYNODE_PING, sn.lastPing.GetHash()));
            nInvCount++;

            if (!mapSeenDynodeBroadcast.count(hash)) {
                mapSeenDynodeBroadcast.insert(std::make_pair(hash, std::make_pair(GetTime(), snb)));
            }

            if (vin == sn.vin) {
                LogPrintf("SSEG -- Sent 1 Dynode inv to peer %d\n", pfrom->id);
                return;
            }
        }

        if(vin == CTxIn()) {
            pfrom->PushMessage(NetMsgType::SYNCSTATUSCOUNT, DYNODE_SYNC_LIST, nInvCount);
            LogPrintf("SSEG -- Sent %d Dynode invs to peer %d\n", nInvCount, pfrom->id);
            return;
        }
        // smth weird happen - someone asked us for vin we have no idea about?
        LogPrint("Dynode", "SSEG -- No invs sent to peer %d\n", pfrom->id);

    } else if (strCommand == NetMsgType::SNVERIFY) { // Dynode Verify

        // Need LOCK2 here to ensure consistent locking order because the all functions below call GetBlockHash which locks cs_main
        LOCK2(cs_main, cs);

        CDynodeVerification snv;
        vRecv >> snv;

        if(snv.vchSig1.empty()) {
            // CASE 1: someone asked me to verify myself /IP we are using/
            SendVerifyReply(pfrom, snv);
        } else if (snv.vchSig2.empty()) {
            // CASE 2: we _probably_ got verification we requested from some Dynode
            ProcessVerifyReply(pfrom, snv);
        } else {
            // CASE 3: we _probably_ got verification broadcast signed by some Dynode which verified another one
            ProcessVerifyBroadcast(pfrom, snv);
        }
    }
}

// Verification of Dynode via unique direct requests.

void CDynodeMan::DoFullVerificationStep()
{
    if(activeDynode.vin == CTxIn()) return;
    if(!dynodeSync.IsSynced()) return;

    std::vector<std::pair<int, CDynode> > vecDynodeRanks = GetDynodeRanks(pCurrentBlockIndex->nHeight - 1, MIN_POSE_PROTO_VERSION);

    // Need LOCK2 here to ensure consistent locking order because the SendVerifyRequest call below locks cs_main
    // through GetHeight() signal in ConnectNode
    LOCK2(cs_main, cs);

    int nCount = 0;

    int nMyRank = -1;
    int nRanksTotal = (int)vecDynodeRanks.size();

    // send verify requests only if we are in top MAX_POSE_RANK
    std::vector<std::pair<int, CDynode> >::iterator it = vecDynodeRanks.begin();
    while(it != vecDynodeRanks.end()) {
        if(it->first > MAX_POSE_RANK) {
            LogPrint("Dynode", "CDynodeMan::DoFullVerificationStep -- Must be in top %d to send verify request\n",
                        (int)MAX_POSE_RANK);
            return;
        }
        if(it->second.vin == activeDynode.vin) {
            nMyRank = it->first;
            LogPrint("Dynode", "CDynodeMan::DoFullVerificationStep -- Found self at rank %d/%d, verifying up to %d Dynodes\n",
                        nMyRank, nRanksTotal, (int)MAX_POSE_CONNECTIONS);
            break;
        }
        ++it;
    }

    // edge case: list is too short and this Dynode is not enabled
    if(nMyRank == -1) return;

    // send verify requests to up to MAX_POSE_CONNECTIONS Dynodes
    // starting from MAX_POSE_RANK + nMyRank and using MAX_POSE_CONNECTIONS as a step
    int nOffset = MAX_POSE_RANK + nMyRank - 1;
    if(nOffset >= (int)vecDynodeRanks.size()) return;

    std::vector<CDynode*> vSortedByAddr;
    BOOST_FOREACH(CDynode& sn, vDynodes) {
        vSortedByAddr.push_back(&sn);
    }

    sort(vSortedByAddr.begin(), vSortedByAddr.end(), CompareByAddr());

    it = vecDynodeRanks.begin() + nOffset;
    while(it != vecDynodeRanks.end()) {
        if(it->second.IsPoSeVerified() || it->second.IsPoSeBanned()) {
            LogPrint("Dynode", "CDynodeMan::DoFullVerificationStep -- Already %s%s%s Dynode %s address %s, skipping...\n",
                        it->second.IsPoSeVerified() ? "verified" : "",
                        it->second.IsPoSeVerified() && it->second.IsPoSeBanned() ? " and " : "",
                        it->second.IsPoSeBanned() ? "banned" : "",
                        it->second.vin.prevout.ToStringShort(), it->second.addr.ToString());
            nOffset += MAX_POSE_CONNECTIONS;
            if(nOffset >= (int)vecDynodeRanks.size()) break;
            it += MAX_POSE_CONNECTIONS;
            continue;
        }
        LogPrint("Dynode", "CDynodeMan::DoFullVerificationStep -- Verifying Dynode %s rank %d/%d address %s\n",
                    it->second.vin.prevout.ToStringShort(), it->first, nRanksTotal, it->second.addr.ToString());
        if(SendVerifyRequest((CAddress)it->second.addr, vSortedByAddr)) {
            nCount++;
            if(nCount >= MAX_POSE_CONNECTIONS) break;
        }
        nOffset += MAX_POSE_CONNECTIONS;
        if(nOffset >= (int)vecDynodeRanks.size()) break;
        it += MAX_POSE_CONNECTIONS;
    }

    LogPrint("Dynode", "CDynodeMan::DoFullVerificationStep -- Sent verification requests to %d Dynodes\n", nCount);
}

// This function tries to find Dynodes with the same addr,
// find a verified one and ban all the other. If there are many nodes
// with the same addr but none of them is verified yet, then none of them are banned.
// It could take many times to run this before most of the duplicate nodes are banned.

void CDynodeMan::CheckSameAddr()
{
    if(!dynodeSync.IsSynced() || vDynodes.empty()) return;

    std::vector<CDynode*> vBan;
    std::vector<CDynode*> vSortedByAddr;

    {
        LOCK(cs);

        CDynode* pprevDynode = NULL;
        CDynode* pverifiedDynode = NULL;

        BOOST_FOREACH(CDynode& sn, vDynodes) {
            vSortedByAddr.push_back(&sn);
        }

        sort(vSortedByAddr.begin(), vSortedByAddr.end(), CompareByAddr());

        BOOST_FOREACH(CDynode* psn, vSortedByAddr) {
            // check only (pre)enabled Dynodes
            if(!psn->IsEnabled() && !psn->IsPreEnabled()) continue;
            // initial step
            if(!pprevDynode) {
                pprevDynode = psn;
                pverifiedDynode = psn->IsPoSeVerified() ? psn : NULL;
                continue;
            }
            // second+ step
            if(psn->addr == pprevDynode->addr) {
                if(pverifiedDynode) {
                    // another Dynode with the same ip is verified, ban this one
                    vBan.push_back(psn);
                } else if(psn->IsPoSeVerified()) {
                    // this Dynode with the same ip is verified, ban previous one
                    vBan.push_back(pprevDynode);
                    // and keep a reference to be able to ban following Dynodes with the same ip
                    pverifiedDynode = psn;
                }
            } else {
                pverifiedDynode = psn->IsPoSeVerified() ? psn : NULL;
            }
            pprevDynode = psn;
        }
    }

    // ban duplicates
    BOOST_FOREACH(CDynode* psn, vBan) {
        LogPrintf("CDynodeMan::CheckSameAddr -- increasing PoSe ban score for Dynode %s\n", psn->vin.prevout.ToStringShort());
        psn->IncreasePoSeBanScore();
    }
}

bool CDynodeMan::SendVerifyRequest(const CAddress& addr, const std::vector<CDynode*>& vSortedByAddr)
{
    if(netfulfilledman.HasFulfilledRequest(addr, strprintf("%s", NetMsgType::SNVERIFY)+"-request")) {
        // we already asked for verification, not a good idea to do this too often, skip it
        LogPrint("Dynode", "CDynodeMan::SendVerifyRequest -- too many requests, skipping... addr=%s\n", addr.ToString());
        return false;
    }

    CNode* pnode = ConnectNode(addr, NULL, true);
    if(pnode == NULL) {
        LogPrintf("CDynodeMan::SendVerifyRequest -- can't connect to node to verify it, addr=%s\n", addr.ToString());
        return false;
    }

    netfulfilledman.AddFulfilledRequest(addr, strprintf("%s", NetMsgType::SNVERIFY)+"-request");
    // use random nonce, store it and require node to reply with correct one later
    CDynodeVerification snv(addr, GetRandInt(999999), pCurrentBlockIndex->nHeight - 1);
    mWeAskedForVerification[addr] = snv;
    LogPrintf("CDynodeMan::SendVerifyRequest -- verifying node using nonce %d addr=%s\n", snv.nonce, addr.ToString());
    pnode->PushMessage(NetMsgType::SNVERIFY, snv);

    return true;
}

void CDynodeMan::SendVerifyReply(CNode* pnode, CDynodeVerification& snv)
{
    // only Dynodes can sign this, why would someone ask regular node?
    if(!fDyNode) {
        // do not ban, malicious node might be using my IP
        // and trying to confuse the node which tries to verify it
        return;
    }

    if(netfulfilledman.HasFulfilledRequest(pnode->addr, strprintf("%s", NetMsgType::SNVERIFY)+"-reply")) {
        // peer should not ask us that often
        LogPrintf("DynodeMan::SendVerifyReply -- ERROR: peer already asked me recently, peer=%d\n", pnode->id);
        Misbehaving(pnode->id, 20);
        return;
    }

    uint256 blockHash;
    if(!GetBlockHash(blockHash, snv.nBlockHeight)) {
        LogPrintf("DynodeMan::SendVerifyReply -- can't get block hash for unknown block height %d, peer=%d\n", snv.nBlockHeight, pnode->id);
        return;
    }

    std::string strMessage = strprintf("%s%d%s", activeDynode.service.ToString(false), snv.nonce, blockHash.ToString());

    if(!privateSendSigner.SignMessage(strMessage, snv.vchSig1, activeDynode.keyDynode)) {
        LogPrintf("DynodeMan::SendVerifyReply -- SignMessage() failed\n");
        return;
    }

    std::string strError;

    if(!privateSendSigner.VerifyMessage(activeDynode.pubKeyDynode, snv.vchSig1, strMessage, strError)) {
        LogPrintf("DynodeMan::SendVerifyReply -- VerifyMessage() failed, error: %s\n", strError);
        return;
    }

    pnode->PushMessage(NetMsgType::SNVERIFY, snv);
    netfulfilledman.AddFulfilledRequest(pnode->addr, strprintf("%s", NetMsgType::SNVERIFY)+"-reply");
}

void CDynodeMan::ProcessVerifyReply(CNode* pnode, CDynodeVerification& snv)
{
    std::string strError;

    // did we even ask for it? if that's the case we should have matching fulfilled request
    if(!netfulfilledman.HasFulfilledRequest(pnode->addr, strprintf("%s", NetMsgType::SNVERIFY)+"-request")) {
        LogPrintf("CDynodeMan::ProcessVerifyReply -- ERROR: we didn't ask for verification of %s, peer=%d\n", pnode->addr.ToString(), pnode->id);
        Misbehaving(pnode->id, 20);
        return;
    }

    // Received nonce for a known address must match the one we sent
    if(mWeAskedForVerification[pnode->addr].nonce != snv.nonce) {
        LogPrintf("CDynodeMan::ProcessVerifyReply -- ERROR: wrong nounce: requested=%d, received=%d, peer=%d\n",
                    mWeAskedForVerification[pnode->addr].nonce, snv.nonce, pnode->id);
        Misbehaving(pnode->id, 20);
        return;
    }

    // Received nBlockHeight for a known address must match the one we sent
    if(mWeAskedForVerification[pnode->addr].nBlockHeight != snv.nBlockHeight) {
        LogPrintf("CDynodeMan::ProcessVerifyReply -- ERROR: wrong nBlockHeight: requested=%d, received=%d, peer=%d\n",
                    mWeAskedForVerification[pnode->addr].nBlockHeight, snv.nBlockHeight, pnode->id);
        Misbehaving(pnode->id, 20);
        return;
    }

    uint256 blockHash;
    if(!GetBlockHash(blockHash, snv.nBlockHeight)) {
        // this shouldn't happen...
        LogPrintf("DynodeMan::ProcessVerifyReply -- can't get block hash for unknown block height %d, peer=%d\n", snv.nBlockHeight, pnode->id);
        return;
    }

    // we already verified this address, why node is spamming?
    if(netfulfilledman.HasFulfilledRequest(pnode->addr, strprintf("%s", NetMsgType::SNVERIFY)+"-done")) {
        LogPrintf("CDynodeMan::ProcessVerifyReply -- ERROR: already verified %s recently\n", pnode->addr.ToString());
        Misbehaving(pnode->id, 20);
        return;
    }

    {
        LOCK(cs);

        CDynode* prealDynode = NULL;
        std::vector<CDynode*> vpDynodesToBan;
        std::vector<CDynode>::iterator it = vDynodes.begin();
        std::string strMessage1 = strprintf("%s%d%s", pnode->addr.ToString(false), snv.nonce, blockHash.ToString());
        while(it != vDynodes.end()) {
            if((CAddress)it->addr == pnode->addr) {
                if(privateSendSigner.VerifyMessage(it->pubKeyDynode, snv.vchSig1, strMessage1, strError)) {
                    // found it!
                    prealDynode = &(*it);
                    if(!it->IsPoSeVerified()) {
                        it->DecreasePoSeBanScore();
                    }
                    netfulfilledman.AddFulfilledRequest(pnode->addr, strprintf("%s", NetMsgType::SNVERIFY)+"-done");

                    // we can only broadcast it if we are an activated Dynode
                    if(activeDynode.vin == CTxIn()) continue;
                    // update ...
                    snv.addr = it->addr;
                    snv.vin1 = it->vin;
                    snv.vin2 = activeDynode.vin;
                    std::string strMessage2 = strprintf("%s%d%s%s%s", snv.addr.ToString(false), snv.nonce, blockHash.ToString(),
                                            snv.vin1.prevout.ToStringShort(), snv.vin2.prevout.ToStringShort());
                    // ... and sign it
                    if(!privateSendSigner.SignMessage(strMessage2, snv.vchSig2, activeDynode.keyDynode)) {
                        LogPrintf("DynodeMan::ProcessVerifyReply -- SignMessage() failed\n");
                        return;
                    }

                    std::string strError;

                    if(!privateSendSigner.VerifyMessage(activeDynode.pubKeyDynode, snv.vchSig2, strMessage2, strError)) {
                        LogPrintf("DynodeMan::ProcessVerifyReply -- VerifyMessage() failed, error: %s\n", strError);
                        return;
                    }

                    mWeAskedForVerification[pnode->addr] = snv;
                    snv.Relay();

                } else {
                    vpDynodesToBan.push_back(&(*it));
                }
            }
            ++it;
        }
        // no real Dynode found?...
        if(!prealDynode) {
            // this should never be the case normally,
            // only if someone is trying to game the system in some way or smth like that
            LogPrintf("CDynodeMan::ProcessVerifyReply -- ERROR: no real Dynode found for addr %s\n", pnode->addr.ToString());
            Misbehaving(pnode->id, 20);
            return;
        }
        LogPrintf("CDynodeMan::ProcessVerifyReply -- verified real Dynode %s for addr %s\n",
                    prealDynode->vin.prevout.ToStringShort(), pnode->addr.ToString());
        // increase ban score for everyone else
        BOOST_FOREACH(CDynode* psn, vpDynodesToBan) {
            psn->IncreasePoSeBanScore();
            LogPrint("Dynode", "CDynodeMan::ProcessVerifyBroadcast -- increased PoSe ban score for %s addr %s, new score %d\n",
                        prealDynode->vin.prevout.ToStringShort(), pnode->addr.ToString(), psn->nPoSeBanScore);
        }
        LogPrintf("CDynodeMan::ProcessVerifyBroadcast -- PoSe score increased for %d fake Dynodes, addr %s\n",
                    (int)vpDynodesToBan.size(), pnode->addr.ToString());
    }
}

void CDynodeMan::ProcessVerifyBroadcast(CNode* pnode, const CDynodeVerification& snv)
{
    std::string strError;

    if(mapSeenDynodeVerification.find(snv.GetHash()) != mapSeenDynodeVerification.end()) {
        // we already have one
        return;
    }
    mapSeenDynodeVerification[snv.GetHash()] = snv;

    // we don't care about history
    if(snv.nBlockHeight < pCurrentBlockIndex->nHeight - MAX_POSE_BLOCKS) {
        LogPrint("Dynode", "DynodeMan::ProcessVerifyBroadcast -- Outdated: current block %d, verification block %d, peer=%d\n",
                    pCurrentBlockIndex->nHeight, snv.nBlockHeight, pnode->id);
        return;
    }

    if(snv.vin1.prevout == snv.vin2.prevout) {
        LogPrint("Dynode", "DynodeMan::ProcessVerifyBroadcast -- ERROR: same vins %s, peer=%d\n",
                    snv.vin1.prevout.ToStringShort(), pnode->id);
        // that was NOT a good idea to cheat and verify itself,
        // ban the node we received such message from
        Misbehaving(pnode->id, 100);
        return;
    }

    uint256 blockHash;
    if(!GetBlockHash(blockHash, snv.nBlockHeight)) {
        // this shouldn't happen...
        LogPrintf("DynodeMan::ProcessVerifyBroadcast -- Can't get block hash for unknown block height %d, peer=%d\n", snv.nBlockHeight, pnode->id);
        return;
    }

    int nRank = GetDynodeRank(snv.vin2, snv.nBlockHeight, MIN_POSE_PROTO_VERSION);
    if(nRank < MAX_POSE_RANK) {
        LogPrint("Dynode", "DynodeMan::ProcessVerifyBroadcast -- Dynode is not in top %d, current rank %d, peer=%d\n",
                    (int)MAX_POSE_RANK, nRank, pnode->id);
        return;
    }

    {
        LOCK(cs);

        std::string strMessage1 = strprintf("%s%d%s", snv.addr.ToString(false), snv.nonce, blockHash.ToString());
        std::string strMessage2 = strprintf("%s%d%s%s%s", snv.addr.ToString(false), snv.nonce, blockHash.ToString(),
                                snv.vin1.prevout.ToStringShort(), snv.vin2.prevout.ToStringShort());

        CDynode* psn1 = Find(snv.vin1);
        if(!psn1) {
            LogPrintf("CDynodeMan::ProcessVerifyBroadcast -- can't find Dynode1 %s\n", snv.vin1.prevout.ToStringShort());
            return;
        }

        CDynode* psn2 = Find(snv.vin2);
        if(!psn2) {
            LogPrintf("CDynodeMan::ProcessVerifyBroadcast -- can't find Dynode %s\n", snv.vin2.prevout.ToStringShort());
            return;
        }

        if(psn1->addr != snv.addr) {
            LogPrintf("CDynodeMan::ProcessVerifyBroadcast -- addr %s do not match %s\n", snv.addr.ToString(), pnode->addr.ToString());
            return;
        }

        if(privateSendSigner.VerifyMessage(psn1->pubKeyDynode, snv.vchSig1, strMessage1, strError)) {
            LogPrintf("DynodeMan::ProcessVerifyBroadcast -- VerifyMessage() for Dynode1 failed, error: %s\n", strError);
            return;
        }

        if(privateSendSigner.VerifyMessage(psn2->pubKeyDynode, snv.vchSig2, strMessage2, strError)) {
            LogPrintf("DynodeMan::ProcessVerifyBroadcast -- VerifyMessage() for Dynode2 failed, error: %s\n", strError);
            return;
        }

        if(!psn1->IsPoSeVerified()) {
            psn1->DecreasePoSeBanScore();
        }
        snv.Relay();

        LogPrintf("CDynodeMan::ProcessVerifyBroadcast -- verified Dynode %s for addr %s\n",
                    psn1->vin.prevout.ToStringShort(), pnode->addr.ToString());

        // increase ban score for everyone else with the same addr
        int nCount = 0;
        BOOST_FOREACH(CDynode& sn, vDynodes) {
            if(sn.addr != snv.addr || sn.vin.prevout == snv.vin1.prevout) continue;
            sn.IncreasePoSeBanScore();
            nCount++;
            LogPrint("Dynode", "CDynodeMan::ProcessVerifyBroadcast -- increased PoSe ban score for %s addr %s, new score %d\n",
                        sn.vin.prevout.ToStringShort(), sn.addr.ToString(), sn.nPoSeBanScore);
        }
        LogPrintf("CDynodeMan::ProcessVerifyBroadcast -- PoSe score incresed for %d fake Dynodes, addr %s\n",
                    nCount, pnode->addr.ToString());
    }
}

std::string CDynodeMan::ToString() const
{
    std::ostringstream info;

    info << "Dynodes: " << (int)vDynodes.size() <<
            ", peers who asked us for Dynode list: " << (int)mAskedUsForDynodeList.size() <<
            ", peers we asked for Dynode list: " << (int)mWeAskedForDynodeList.size() <<
            ", entries in Dynode list we asked for: " << (int)mWeAskedForDynodeListEntry.size() <<
            ", dynode index size: " << indexDynodes.GetSize() <<
            ", nSsqCount: " << (int)nSsqCount;

    return info.str();
}

void CDynodeMan::UpdateDynodeList(CDynodeBroadcast snb)
{
    LOCK(cs);
    mapSeenDynodePing.insert(std::make_pair(snb.lastPing.GetHash(), snb.lastPing));
    mapSeenDynodeBroadcast.insert(std::make_pair(snb.GetHash(), std::make_pair(GetTime(), snb)));

    LogPrintf("CDynodeMan::UpdateDynodeList -- Dynode=%s  addr=%s\n", snb.vin.prevout.ToStringShort(), snb.addr.ToString());

    CDynode* psn = Find(snb.vin);
    if(psn == NULL) {
        CDynode sn(snb);
        if(Add(sn)) {
            dynodeSync.AddedDynodeList();
        }
    } else {
        CDynodeBroadcast snbOld = mapSeenDynodeBroadcast[CDynodeBroadcast(*psn).GetHash()].second;
        if(psn->UpdateFromNewBroadcast(snb)) {
            dynodeSync.AddedDynodeList();
            mapSeenDynodeBroadcast.erase(snbOld.GetHash());
        }
    }
}

bool CDynodeMan::CheckSnbAndUpdateDynodeList(CNode* pfrom, CDynodeBroadcast snb, int& nDos)
{
    // Need LOCK2 here to ensure consistent locking order because the SimpleCheck call below locks cs_main
    LOCK2(cs_main, cs);

    nDos = 0;
    LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- Dynode=%s\n", snb.vin.prevout.ToStringShort());

    uint256 hash = snb.GetHash();
    if(mapSeenDynodeBroadcast.count(hash) && !snb.fRecovery) { //seen      
        LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- Dynode=%s seen\n", snb.vin.prevout.ToStringShort());
        // less then 2 pings left before this SN goes into non-recoverable state, bump sync timeout
        if(GetTime() - mapSeenDynodeBroadcast[hash].first > DYNODE_NEW_START_REQUIRED_SECONDS - DYNODE_MIN_SNP_SECONDS * 2) {
            LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- Dynode=%s seen update\n", snb.vin.prevout.ToStringShort());
            mapSeenDynodeBroadcast[hash].first = GetTime();
            dynodeSync.AddedDynodeList();
        }
        // did we ask this node for it?
        if(pfrom && IsSnbRecoveryRequested(hash) && GetTime() < mSnbRecoveryRequests[hash].first) {
            LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- snb=%s seen request\n", hash.ToString());
            if(mSnbRecoveryRequests[hash].second.count(pfrom->addr)) {
                LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- snb=%s seen request, addr=%s\n", hash.ToString(), pfrom->addr.ToString());
                // do not allow node to send same snb multiple times in recovery mode
                mSnbRecoveryRequests[hash].second.erase(pfrom->addr);
                // does it have newer lastPing?
                if(snb.lastPing.sigTime > mapSeenDynodeBroadcast[hash].second.lastPing.sigTime) {
                    // simulate Check
                    CDynode snTemp = CDynode(snb);
                    snTemp.Check();
                    LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- snb=%s seen request, addr=%s, better lastPing: %d min ago, projected sn state: %s\n", hash.ToString(), pfrom->addr.ToString(), (GetTime() - snb.lastPing.sigTime)/60, snTemp.GetStateString());
                    if(snTemp.IsValidStateForAutoStart(snTemp.nActiveState)) {
                        // this node thinks it's a good one
                        LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- Dynode=%s seen good\n", snb.vin.prevout.ToStringShort());
                        mSnbRecoveryGoodReplies[hash].push_back(snb);
                    }
                }
            }
        }
        return true;
    }
    mapSeenDynodeBroadcast.insert(std::make_pair(hash, std::make_pair(GetTime(), snb)));

    LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- Dynode=%s new\n", snb.vin.prevout.ToStringShort());

    if(!snb.SimpleCheck(nDos)) {
        LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- SimpleCheck() failed, Dynode=%s\n", snb.vin.prevout.ToStringShort());
        return false;
    }

    // search Dynode list
    CDynode* psn = Find(snb.vin);
    if(psn) {
        CDynodeBroadcast snbOld = mapSeenDynodeBroadcast[CDynodeBroadcast(*psn).GetHash()].second;
        if(!snb.Update(psn, nDos)) {
            LogPrint("Dynode", "CDynodeMan::CheckSnbAndUpdateDynodeList -- Update() failed, Dynode=%s\n", snb.vin.prevout.ToStringShort());
            return false;
        }
        if(hash != snbOld.GetHash()) {
            mapSeenDynodeBroadcast.erase(snbOld.GetHash());
        }
    } else {
        if(snb.CheckOutpoint(nDos)) {
            Add(snb);
            dynodeSync.AddedDynodeList();
            // if it matches our Dynode privkey...
            if(fDyNode && snb.pubKeyDynode == activeDynode.pubKeyDynode) {
                snb.nPoSeBanScore = -DYNODE_POSE_BAN_MAX_SCORE;
                if(snb.nProtocolVersion == PROTOCOL_VERSION) {
                    // ... and PROTOCOL_VERSION, then we've been remotely activated ...
                    LogPrintf("CDynodeMan::CheckSnbAndUpdateDynodeList -- Got NEW Dynode entry: Dynode=%s  sigTime=%lld  addr=%s\n",
                                snb.vin.prevout.ToStringShort(), snb.sigTime, snb.addr.ToString());
                    activeDynode.ManageState();
                } else {
                    // ... otherwise we need to reactivate our node, do not add it to the list and do not relay
                    // but also do not ban the node we get this message from
                    LogPrintf("CDynodeMan::CheckSnbAndUpdateDynodeList -- wrong PROTOCOL_VERSION, re-activate your SN: message nProtocolVersion=%d  PROTOCOL_VERSION=%d\n", snb.nProtocolVersion, PROTOCOL_VERSION);
                    return false;
                }
            }
            snb.Relay();
        } else {
            LogPrintf("CDynodeMan::CheckSnbAndUpdateDynodeList -- Rejected Dynode entry: %s  addr=%s\n", snb.vin.prevout.ToStringShort(), snb.addr.ToString());
            return false;
        }
    }

    return true;
}

void CDynodeMan::UpdateLastPaid()
{
    LOCK(cs);

    if(fLiteMode) return;
    if(!pCurrentBlockIndex) return;

    static bool IsFirstRun = true;
    // Do full scan on first run or if we are not a Dynode
    // (MNs should update this info on every block, so limited scan should be enough for them)
    int nMaxBlocksToScanBack = (IsFirstRun || !fDyNode) ? snpayments.GetStorageLimit() : LAST_PAID_SCAN_BLOCKS;

    // pCurrentBlockIndex->nHeight, nMaxBlocksToScanBack, IsFirstRun ? "true" : "false");

    BOOST_FOREACH(CDynode& sn, vDynodes) {
        sn.UpdateLastPaid(pCurrentBlockIndex, nMaxBlocksToScanBack);
    }

    // every time is like the first time if winners list is not synced
    IsFirstRun = !dynodeSync.IsWinnersListSynced();
}

void CDynodeMan::CheckAndRebuildDynodeIndex()
{
    LOCK(cs);

    if(GetTime() - nLastIndexRebuildTime < MIN_INDEX_REBUILD_TIME) {
        return;
    }

    if(indexDynodes.GetSize() <= MAX_EXPECTED_INDEX_SIZE) {
        return;
    }

    if(indexDynodes.GetSize() <= int(vDynodes.size())) {
        return;
    }

    indexDynodesOld = indexDynodes;
    indexDynodes.Clear();
    for(size_t i = 0; i < vDynodes.size(); ++i) {
        indexDynodes.AddDynodeVIN(vDynodes[i].vin);
    }

    fIndexRebuilt = true;
    nLastIndexRebuildTime = GetTime();
}

void CDynodeMan::UpdateWatchdogVoteTime(const CTxIn& vin)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return;
    }
    pSN->UpdateWatchdogVoteTime();
    nLastWatchdogVoteTime = GetTime();
}

bool CDynodeMan::IsWatchdogActive()
{
    LOCK(cs);
    // Check if any Dynodes have voted recently, otherwise return false
    return (GetTime() - nLastWatchdogVoteTime) <= DYNODE_WATCHDOG_MAX_SECONDS;
}

void CDynodeMan::AddGovernanceVote(const CTxIn& vin, uint256 nGovernanceObjectHash)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return;
    }
    pSN->AddGovernanceVote(nGovernanceObjectHash);
}

void CDynodeMan::RemoveGovernanceObject(uint256 nGovernanceObjectHash)
{
    LOCK(cs);
    BOOST_FOREACH(CDynode& sn, vDynodes) {
        sn.RemoveGovernanceObject(nGovernanceObjectHash);
    }
}

void CDynodeMan::CheckDynode(const CTxIn& vin, bool fForce)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return;
    }
    pSN->Check(fForce);
}

void CDynodeMan::CheckDynode(const CPubKey& pubKeyDynode, bool fForce)
{
    LOCK(cs);
    CDynode* pSN = Find(pubKeyDynode);
    if(!pSN)  {
        return;
    }
    pSN->Check(fForce);
}

int CDynodeMan::GetDynodeState(const CTxIn& vin)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return CDynode::DYNODE_NEW_START_REQUIRED;
    }
    return pSN->nActiveState;
}

int CDynodeMan::GetDynodeState(const CPubKey& pubKeyDynode)
{
    LOCK(cs);
    CDynode* pSN = Find(pubKeyDynode);
    if(!pSN)  {
        return CDynode::DYNODE_NEW_START_REQUIRED;
    }
    return pSN->nActiveState;
}

bool CDynodeMan::IsDynodePingedWithin(const CTxIn& vin, int nSeconds, int64_t nTimeToCheckAt)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN) {
        return false;
    }
    return pSN->IsPingedWithin(nSeconds, nTimeToCheckAt);
}

void CDynodeMan::SetDynodeLastPing(const CTxIn& vin, const CDynodePing& snp)
{
    LOCK(cs);
    CDynode* pSN = Find(vin);
    if(!pSN)  {
        return;
    }
    pSN->lastPing = snp;
    mapSeenDynodePing.insert(std::make_pair(snp.GetHash(), snp));

    CDynodeBroadcast snb(*pSN);
    uint256 hash = snb.GetHash();
    if(mapSeenDynodeBroadcast.count(hash)) {
        mapSeenDynodeBroadcast[hash].second.lastPing = snp;
    }
}

void CDynodeMan::UpdatedBlockTip(const CBlockIndex *pindex)
{
    pCurrentBlockIndex = pindex;
    LogPrint("Dynode", "CDynodeMan::UpdatedBlockTip -- pCurrentBlockIndex->nHeight=%d\n", pCurrentBlockIndex->nHeight);

    CheckSameAddr();

    if(fDyNode) {
        // normal wallet does not need to update this every block, doing update on rpc call should be enough
        UpdateLastPaid();
    }
}

void CDynodeMan::NotifyDynodeUpdates()
{
    // Avoid double locking
    bool fDynodesAddedLocal = false;
    bool fDynodesRemovedLocal = false;
    {
        LOCK(cs);
        fDynodesAddedLocal = fDynodesAdded;
        fDynodesRemovedLocal = fDynodesRemoved;
    }

    if(fDynodesAddedLocal) {
        governance.CheckDynodeOrphanObjects();
        governance.CheckDynodeOrphanVotes();
    }
    if(fDynodesRemovedLocal) {
        governance.UpdateCachesAndClean();
    }

    LOCK(cs);
    fDynodesAdded = false;
    fDynodesRemoved = false;
}
