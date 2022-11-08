----------------------------- MODULE BossWorker -----------------------------

(***************************************************************************)
(* Copyright 2022 Cartesi Pte. Ltd.                                        *)
(*                                                                         *)
(* Licensed under the Apache License, Version 2.0 (the "License"); you may *)
(* not use this file except in compliance with the License. You may obtain *)
(* a copy of the License at http://www.apache.org/licenses/LICENSE-2.0     *)
(*                                                                         *)
(* Unless required by applicable law or agreed to in writing, software     *)
(* distributed under the License is distributed on an "AS IS" BASIS,       *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or         *)
(* implied. See the License for the specific language governing            *)
(* permissions and limitations under the License.                          *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Specification of the BossWorker smart contract                          *)
(*                                                                         *)
(* The Claim Validation phase is an abstract time window estipulated by    *)
(* the boss off-chain, which in reality is contained within the Claim      *)
(* Suggestion phase on-chain. In this time window, the boss wakes up and   *)
(* decides whether the current suggested claim is valid or not.            *)
(*                                                                         *)
(* If the boss finds that a claim has not been suggested for this epoch,   *)
(* or that the suggested claim is wrong, they should hire a new worker in  *)
(* just enough time to validate its suggested claim.                       *)
(***************************************************************************)

CONSTANT
    noWorker,     \* address(0)
    validWorkers, \* valid addresses
    noClaim,      \* bytes32(0)
    validClaims   \* valid byte32 values

ASSUME
    /\ noWorker \notin validWorkers
    /\ noClaim \notin validClaims

VARIABLES
    rollupsEpoch,      \* rollups epoch index
    rollupsEpochHash,  \* correct rollups epoch hash
    bwPhase,           \* boss worker view of rollups phases
    bwWorker,          \* worker
    bwSuggestedClaim,  \* last suggested claim
    bwEpoch,           \* epoch of last suggested claim
    bwClaimer,         \* worker that made last suggested claim
    bwIsClaimValidated \* whether the boss (off-chain) is ok with suggested claim

(***************************************************************************)
(* Useful global definitions                                               *)
(***************************************************************************)

BossWorkerPhase ==
    {"InputAccumulation", \* receiving inputs (epoch hash may change)
     "ClaimSuggestion",   \* workers can suggest claims and the boss is idle
     "ClaimValidation",   \* workers can suggest claims and the boss is active
     "ClaimSubmission"}   \* anyone can submit suggested claims

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK ==
    /\ bwPhase \in BossWorkerPhase
    /\ rollupsEpoch \in Nat
    /\ rollupsEpochHash \in validClaims
    /\ bwWorker \in validWorkers \cup {noWorker}
    /\ bwSuggestedClaim \in validClaims \cup {noClaim}
    /\ bwEpoch \in Nat
    /\ bwClaimer \in validWorkers \cup {noWorker}
    /\ bwIsClaimValidated \in BOOLEAN

CanUserSubmitClaim ==
    /\ bwPhase = "ClaimSubmission"
    /\ bwClaimer = bwWorker
    /\ bwEpoch = rollupsEpoch
    /\ bwSuggestedClaim \in validClaims

SuggestedClaimIsCorrect ==
    bwSuggestedClaim = rollupsEpochHash

SubmittableClaimIsCorrect ==
    CanUserSubmitClaim => SuggestedClaimIsCorrect

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
    /\ rollupsEpoch = 0
    /\ rollupsEpochHash \in validClaims \* could be in any machine state
    /\ bwPhase \in BossWorkerPhase \* could be in any boss worker phase
    /\ bwWorker = noWorker
    /\ bwSuggestedClaim = noClaim
    /\ bwEpoch = 0
    /\ bwClaimer = noWorker
    /\ bwIsClaimValidated = FALSE

(***************************************************************************)
(* Worker behaviour                                                        *)
(***************************************************************************)

SuggestClaim ==
    /\ bwWorker \in validWorkers \* (there must be a valid worker)
    (**********************************************************************)
    (* Workers cannot suggest a claim if they have already done so, since *)
    (* this would allow workers to submit bad claims right on the end of  *)
    (* the ClaimSuggestion phase, leaving the boss with no reaction time. *)
    (**********************************************************************)
    /\ ~ (bwClaimer = bwWorker /\ bwEpoch = rollupsEpoch)
    /\ bwPhase \in {"ClaimSuggestion", "ClaimValidation"}
    /\ bwSuggestedClaim' \in validClaims
    /\ bwEpoch' = rollupsEpoch
    /\ bwClaimer' = bwWorker
    /\ UNCHANGED <<rollupsEpoch,
                   rollupsEpochHash,
                   bwPhase,
                   bwWorker,
                   bwIsClaimValidated>>

(***************************************************************************)
(* Boss behaviour                                                          *)
(***************************************************************************)

SetWorker ==
    /\ bwWorker' \in validWorkers \cup {noWorker}
       (* boss has no reason to change worker if the claim has been validated *)
    /\ bwIsClaimValidated = FALSE
    /\ UNCHANGED <<rollupsEpoch, 
                   rollupsEpochHash,
                   bwPhase,
                   bwSuggestedClaim,
                   bwEpoch,
                   bwClaimer,
                   bwIsClaimValidated>>

ValidateClaim ==
    /\ bwPhase = "ClaimValidation"
    /\ bwIsClaimValidated = FALSE
    /\ bwSuggestedClaim = rollupsEpochHash
    /\ bwClaimer = bwWorker
    /\ bwEpoch = rollupsEpoch
    /\ bwIsClaimValidated' = TRUE
    /\ UNCHANGED <<rollupsEpoch,
                   rollupsEpochHash,
                   bwPhase,
                   bwWorker,
                   bwSuggestedClaim,
                   bwEpoch,
                   bwClaimer>>

(***************************************************************************)
(* User behaviour                                                          *)
(***************************************************************************)

AddInput ==
    /\ bwPhase = "InputAccumulation"
    /\ rollupsEpochHash' \in validClaims \* (machine hash changes)
    /\ UNCHANGED <<rollupsEpoch,
                   bwPhase,
                   bwWorker,
                   bwSuggestedClaim,
                   bwEpoch,
                   bwClaimer,
                   bwIsClaimValidated>>

(***************************************************************************)
(* Rollups behaviour                                                       *)
(***************************************************************************)

NextPhase ==
   \/ /\ bwPhase = "InputAccumulation"
      /\ bwPhase' = "ClaimSuggestion"
      /\ UNCHANGED <<rollupsEpoch,
                     rollupsEpochHash,
                     bwWorker,
                     bwSuggestedClaim,
                     bwEpoch,
                     bwClaimer,
                     bwIsClaimValidated>>
   \/ /\ bwPhase = "ClaimSuggestion"
      /\ bwPhase' = "ClaimValidation"
      /\ UNCHANGED <<rollupsEpoch,
                     rollupsEpochHash,
                     bwWorker,
                     bwSuggestedClaim,
                     bwEpoch,
                     bwClaimer,
                     bwIsClaimValidated>>
   \/ /\ bwPhase = "ClaimValidation"
      /\ bwIsClaimValidated = TRUE
      /\ bwPhase' = "ClaimSubmission"
      /\ UNCHANGED <<rollupsEpoch,
                     rollupsEpochHash,
                     bwWorker,
                     bwSuggestedClaim,
                     bwEpoch,
                     bwClaimer,
                     bwIsClaimValidated>>
   \/ /\ bwPhase = "ClaimSubmission"
      /\ bwPhase' = "InputAccumulation"
      /\ bwIsClaimValidated' = FALSE
      /\ rollupsEpoch' = rollupsEpoch + 1
      /\ UNCHANGED <<rollupsEpochHash,
                     bwWorker,
                     bwSuggestedClaim,
                     bwEpoch,
                     bwClaimer>>

(***************************************************************************)
(* Next state                                                              *)
(***************************************************************************)

Next ==
    \/ SetWorker
    \/ AddInput
    \/ SuggestClaim
    \/ ValidateClaim
    \/ NextPhase

=============================================================================
\* Modification History
\* Last modified Wed Jun 22 00:09:56 BRT 2022 by guilherme
\* Created Mon May 30 11:40:33 BRT 2022 by guilherme
