// Copyright (c) 2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "consensus.h"

#include "pow.h"
#include "primitives/block.h"
#include "tinyformat.h"
#include "validation.h"
#include "chainparams.h"

#include "timedata.h"
#include "util.h"
#include "utilmoneystr.h"

// TODO remove the following dependencies
#include "chain.h"

bool CheckBlockHeader(const CBlockHeader& block, CValidationState& state, bool fCheckPOW)
{
    // Check proof of work matches claimed amount
    if (fCheckPOW && !CheckProofOfWork(block.GetHash(), block.nBits, Params().GetConsensus()))
        return state.DoS(50, error("CheckBlockHeader(): proof of work failed"),
                         REJECT_INVALID, "high-hash");

    // Check timestamp
    if (block.GetBlockTime() > GetAdjustedTime() + 2 * 60 * 60)
        return state.Invalid(error("CheckBlockHeader(): block timestamp too far in the future"),
                             REJECT_INVALID, "time-too-new");

    return true;
}

bool ContextualCheckBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex * const pindexPrev)
{   
    uint256 hash = block.GetHash();
    
    if (hash == Params().GetConsensus().hashGenesisBlock)
        return true;

    const Consensus::Params& consensusParams = Params().GetConsensus();
    int nHeight = pindexPrev->nHeight + 1;
    
    if(Params().NetworkIDString() == CBaseChainParams::TESTNET) {
    if (block.nBits != GetNextWorkRequired(pindexPrev, &block, consensusParams))
        return state.DoS(100, error("%s : incorrect proof of work at %d", __func__, nHeight),
                            REJECT_INVALID, "bad-diffbits");
    } else {
    if (block.nBits != GetNextWorkRequired(pindexPrev, &block, consensusParams))
        return state.DoS(100, error("%s : incorrect proof of work at %d", __func__, nHeight),
                        REJECT_INVALID, "bad-diffbits");
    }

    // Check timestamp against prev
    if (block.GetBlockTime() <= pindexPrev->GetMedianTimePast())
        return state.Invalid(error("%s: block's timestamp is too early", __func__),
                             REJECT_INVALID, "time-too-old");
    return true;
}
