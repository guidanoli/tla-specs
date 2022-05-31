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

CONSTANT possibleWorkers, possibleClaims, emptyClaim
VARIABLES rollupsPhase, workerStatus, correctClaim, claim

(***************************************************************************)
(* Useful global definitions                                               *)
(***************************************************************************)

RollupsPhase == 
    {"InputAccumulation", \* receiving inputs
     "ClaimSuggestion",   \* accepting suggestions from workers
     "ClaimValidation",   \* validating claims suggested by workers
     "ClaimSubmission"}   \* workers can submit claim

WorkerStatus ==
    {"Unemployed", \* worker does nothing
     "Employed"}   \* worker can suggest and submit claims

TypeOK ==
    /\ workerStatus \in [possibleWorkers -> WorkerStatus]
    /\ rollupsPhase \in RollupsPhase
    /\ correctClaim \in possibleClaims
    /\ emptyClaim \notin possibleClaims
    /\ claim \in possibleClaims \union {emptyClaim}
    /\ Cardinality({ worker \in possibleWorkers : workerStatus[worker] = "Employed" }) \in {0, 1}

(***************************************************************************)
(* Initial state definition                                                *)
(***************************************************************************)

Init ==
    /\ workerStatus = [worker \in possibleWorkers |-> "Unemployed"]
    /\ rollupsPhase \in RollupsPhase
    /\ correctClaim \in possibleClaims
    /\ claim = emptyClaim

(***************************************************************************)
(* Worker status changes                                                   *)
(***************************************************************************)

HireWorker ==
    /\ ~ \E worker \in possibleWorkers :
        workerStatus[worker] = "Employed"
    /\ \E worker \in possibleWorkers :
        /\ workerStatus[worker] = "Unemployed"
        /\ workerStatus' = [workerStatus EXCEPT ![worker] = "Employed"]
        /\ UNCHANGED <<rollupsPhase, correctClaim, claim>>

FireWorker ==
    \E worker \in possibleWorkers :
        /\ workerStatus[worker] = "Employed"
        /\ workerStatus' = [workerStatus EXCEPT ![worker] = "Unemployed"]
        /\ UNCHANGED <<rollupsPhase, correctClaim, claim>>

(***************************************************************************)
(* Rollups phase-related changes                                           *)
(***************************************************************************)

SendInput ==
    /\ rollupsPhase = "InputAccumulation"
    /\ correctClaim' \in possibleClaims \* (machine hash changes)
    /\ UNCHANGED <<rollupsPhase, workerStatus, claim>>

SuggestClaim ==
    \E worker \in possibleWorkers:
        /\ workerStatus[worker] = "Employed"
        /\ rollupsPhase = "ClaimSuggestion"
        /\ claim' \in possibleClaims \* (the order of claims is ignored)
        /\ UNCHANGED <<rollupsPhase, workerStatus, correctClaim>>

NextPhase ==
   \/ /\ rollupsPhase = "InputAccumulation"
      /\ rollupsPhase' = "ClaimSuggestion"
      /\ UNCHANGED <<workerStatus, correctClaim, claim>>
   \/ /\ rollupsPhase = "ClaimSuggestion"
      /\ rollupsPhase' = "ClaimSubmission"
      /\ UNCHANGED <<workerStatus, correctClaim, claim>>
   \/ /\ rollupsPhase = "ClaimSubmission"
      /\ rollupsPhase' = "InputAccumulation"
      /\ claim' = emptyClaim
      /\ UNCHANGED <<workerStatus, correctClaim>>

(***************************************************************************)
(* Next state definition                                                   *)
(***************************************************************************)

Next ==
    \/ HireWorker
    \/ FireWorker
    \/ SendInput
    \/ SuggestClaim
    \/ NextPhase

=============================================================================
\* Modification History
\* Last modified Tue May 31 15:52:57 BRT 2022 by guilherme
\* Created Mon May 30 11:40:33 BRT 2022 by guilherme
