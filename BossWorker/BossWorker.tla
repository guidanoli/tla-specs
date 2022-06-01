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
(***************************************************************************)

CONSTANT possibleWorkers, possibleClaims
VARIABLES rollupsPhase, workerStatus, correctClaim, claimStatus, bossStatus

(***************************************************************************)
(* Useful global definitions                                               *)
(***************************************************************************)

RollupsPhase ==
    {"InputAccumulation", \* receiving inputs (correct claim may change)
     "ClaimSuggestion",   \* workers can suggest claims and the boss can remove them
     "ClaimSubmission"}   \* anyone can submit suggested claims

WorkerStatus ==
    {"Unemployed", \* worker does nothing
     "Employed"}   \* worker can suggest claims

ClaimStatus ==
    {"NotSuggested", \* no worker has suggested such claim
     "Suggested"}    \* some worker has suggested this claim

BossStatus ==
    {"Idle",     \* boss is not prompted to do anything
     "Prompted", \* boss is prompted to validate suggested claims
     "NotHappy", \* boss is not happy with claim
     "Happy"}    \* boss is happy with claim (final state until new epoch)

EmployedWorkers ==
    { worker \in possibleWorkers : workerStatus[worker] = "Employed" }

UnemployedWorkers ==
    { worker \in possibleWorkers : workerStatus[worker] = "Unemployed" }

SuggestedClaims ==
    { claim \in possibleClaims : claimStatus[claim] = "Suggested" }

EmptyClaimStatus ==
    [ claim \in possibleClaims |-> "NotSuggested" ]

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOK ==
    /\ workerStatus \in [possibleWorkers -> WorkerStatus]
    /\ claimStatus \in [possibleClaims -> ClaimStatus]
    /\ bossStatus \in BossStatus
    /\ rollupsPhase \in RollupsPhase
    /\ correctClaim \in possibleClaims
    /\ Cardinality(SuggestedClaims) \in {0, 1}
    /\ Cardinality(EmployedWorkers) \in {0, 1}

CorrectSubmittableClaim ==
    rollupsPhase = "ClaimSubmission" =>
        \A claim \in SuggestedClaims : claim = correctClaim

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
    /\ workerStatus = [worker \in possibleWorkers |-> "Unemployed"]
    /\ claimStatus = EmptyClaimStatus
    /\ rollupsPhase \in RollupsPhase
    /\ correctClaim \in possibleClaims
    /\ bossStatus = "Idle"

(***************************************************************************)
(* Worker behaviour                                                        *)
(***************************************************************************)

WorkerSuggestsClaim ==
    \E worker \in EmployedWorkers :
        \E newClaim \in possibleClaims :
            /\ rollupsPhase = "ClaimSuggestion"
            /\ SuggestedClaims = {} \* (cannot suggest twice)
            /\ claimStatus' = [EmptyClaimStatus EXCEPT ![newClaim] = "Suggested"]
            /\ UNCHANGED <<rollupsPhase, workerStatus, correctClaim, bossStatus>>

(***************************************************************************)
(* Boss behaviour                                                          *)
(***************************************************************************)

BossHiresWorker ==
    \E worker \in UnemployedWorkers :
        (**********************************************************************)
        (* The boss should not hire a worker while prompted because then a    *)
        (* malicious worker might be able to suggest a bad claim leaving the  *)
        (* boss with too little time to fire him and to remove the claim      *)
        (**********************************************************************)
        /\ bossStatus = "Idle"
        /\ EmployedWorkers = {} \* (cannot have multiple workers at the same time)
        /\ workerStatus' = [workerStatus EXCEPT ![worker] = "Employed"]
        /\ UNCHANGED <<rollupsPhase, correctClaim, claimStatus, bossStatus>>

BossFiresWorkerAndRemovesClaim ==
    \E worker \in EmployedWorkers :
        /\ claimStatus' = EmptyClaimStatus
        /\ workerStatus' = [workerStatus EXCEPT ![worker] = "Unemployed"]
        /\ UNCHANGED <<rollupsPhase, correctClaim, bossStatus>>

BossIsPrompted ==
    /\ rollupsPhase = "ClaimSuggestion"
    /\ bossStatus = "Idle"
    /\ bossStatus' = "Prompted"
    /\ UNCHANGED <<rollupsPhase, correctClaim, claimStatus, workerStatus>>

BossValidatesClaim ==
    /\ rollupsPhase = "ClaimSuggestion"
    /\ bossStatus = "Prompted"
    /\ IF correctClaim \in SuggestedClaims
       THEN bossStatus' = "Happy"
       ELSE bossStatus' = "NotHappy"
    /\ UNCHANGED <<rollupsPhase, correctClaim, claimStatus, workerStatus>>

BossGetsHappy ==
    /\ rollupsPhase = "ClaimSuggestion"
    /\ bossStatus = "NotHappy"
    /\ EmployedWorkers = {} \* worker was fired
    /\ SuggestedClaims = {} \* claim was removed
    /\ bossStatus' = "Happy"
    /\ UNCHANGED <<rollupsPhase, correctClaim, claimStatus, workerStatus>>

(***************************************************************************)
(* User behaviour                                                          *)
(***************************************************************************)

UserSendsInput ==
    /\ rollupsPhase = "InputAccumulation"
    /\ correctClaim' \in possibleClaims \* (machine hash changes)
    /\ UNCHANGED <<rollupsPhase, workerStatus, claimStatus, bossStatus>>

UserSubmitsClaim ==
    \E claim \in SuggestedClaims :
        /\ rollupsPhase = "ClaimSubmission"
        /\ claimStatus' = EmptyClaimStatus \* (new epoch, new claims)
        /\ UNCHANGED <<rollupsPhase, workerStatus, correctClaim, bossStatus>>

(***************************************************************************)
(* Rollups behaviour                                                       *)
(***************************************************************************)

NextPhase ==
   \/ /\ rollupsPhase = "InputAccumulation"
      /\ rollupsPhase' = "ClaimSuggestion"
      /\ UNCHANGED <<workerStatus, correctClaim, claimStatus, bossStatus>>
   \/ /\ rollupsPhase = "ClaimSuggestion"
      /\ bossStatus = "Happy" \* (we assume the boss has enough time)
      /\ rollupsPhase' = "ClaimSubmission"
      /\ UNCHANGED <<workerStatus, correctClaim, claimStatus, bossStatus>>
   \/ /\ rollupsPhase = "ClaimSubmission"
      /\ rollupsPhase' = "InputAccumulation"
      /\ bossStatus' = "Idle"
      /\ UNCHANGED <<workerStatus, correctClaim, claimStatus>>

(***************************************************************************)
(* Next state                                                              *)
(***************************************************************************)

Next ==
    \/ BossHiresWorker
    \/ BossFiresWorkerAndRemovesClaim
    \/ BossIsPrompted
    \/ BossValidatesClaim
    \/ BossGetsHappy
    \/ UserSendsInput
    \/ WorkerSuggestsClaim
    \/ UserSubmitsClaim
    \/ NextPhase

=============================================================================
\* Modification History
\* Last modified Wed Jun 01 00:36:17 BRT 2022 by guilherme
\* Created Mon May 30 11:40:33 BRT 2022 by guilherme
