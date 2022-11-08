---------------------------- MODULE RollupsPhase ----------------------------

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

(***************************************************************************)
(* Specification of the Rollups phase changes                              *)
(***************************************************************************)

VARIABLES phase,
          inputAccumulationPeriodOver, 
          challengePeriodOver,
          hasClaim,
          epochIsSealed

(***************************************************************************)
(* Useful global definitions                                               *)
(***************************************************************************)

Phase ==
    {"InputAccumulation",
     "AwaitingConsensus",
     "AwaitingDispute"}

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

RPTypeOK ==
    /\ phase \in Phase
    /\ inputAccumulationPeriodOver \in BOOLEAN
    /\ challengePeriodOver \in BOOLEAN
    /\ hasClaim \in BOOLEAN
    /\ epochIsSealed \in BOOLEAN

RPConsistent ==
    /\ challengePeriodOver => epochIsSealed
    /\ epochIsSealed => inputAccumulationPeriodOver
    /\ phase = "InputAccumulation" <=> epochIsSealed = FALSE
    /\ phase = "InputAccumulation" => hasClaim = FALSE
    /\ phase = "AwaitingDispute" => hasClaim = TRUE
    /\ phase = "InputAccumulation" <=> epochIsSealed = FALSE
    /\ phase = "InputAccumulation" => hasClaim = FALSE
    /\ phase = "AwaitingDispute" => hasClaim = TRUE

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
    /\ phase = "InputAccumulation"
    /\ inputAccumulationPeriodOver = FALSE
    /\ challengePeriodOver = FALSE
    /\ hasClaim = FALSE
    /\ epochIsSealed = FALSE

(***************************************************************************)
(* Next state                                                              *)
(***************************************************************************)

EndInputAccumulationPeriod ==
    /\ inputAccumulationPeriodOver = FALSE
    /\ inputAccumulationPeriodOver' = TRUE
    /\ UNCHANGED << phase, challengePeriodOver, hasClaim, epochIsSealed >>

EndChallengePeriod ==
    /\ epochIsSealed = TRUE
    /\ challengePeriodOver = FALSE
    /\ challengePeriodOver' = TRUE
    /\ UNCHANGED << phase, inputAccumulationPeriodOver, hasClaim, epochIsSealed >>

AddInput ==
    /\ phase = "InputAccumulation"
    /\ IF inputAccumulationPeriodOver
       THEN /\ phase' = "AwaitingConsensus"
            /\ epochIsSealed' = TRUE
       ELSE UNCHANGED << phase, epochIsSealed >>
    /\ UNCHANGED << inputAccumulationPeriodOver, challengePeriodOver, hasClaim >>

(***************************************************************************)
(* We are abstracting away the validator from the specification, but a     *)
(* richer specification should keep track of claims from each validator    *)
(* so that they can't claim twice                                          *)
(***************************************************************************)

Claim ==
    \/ (***************************************************************************)
       (* The input accumulation period is over, no user has sent an input yet,   *)
       (* and a validator has submitted a claim, which changes the current phase. *)
       (* Since it is the first claim, there is no conflict.                      *)
       (***************************************************************************) 
       /\ phase = "InputAccumulation"
       /\ inputAccumulationPeriodOver = TRUE
       /\ phase' = "AwaitingConsensus"
       /\ epochIsSealed' = TRUE
       /\ hasClaim' = TRUE
       /\ UNCHANGED << inputAccumulationPeriodOver, challengePeriodOver >>
    \/ (***************************************************************************)
       (* A late input has arrived and no validator has claimed yet               *)
       (* Since it is the first claim, there is no conflict.                      *)
       (***************************************************************************)
       /\ phase = "AwaitingConsensus"
       /\ hasClaim = FALSE
       /\ hasClaim' = TRUE
       /\ UNCHANGED << phase, inputAccumulationPeriodOver, challengePeriodOver, epochIsSealed >>
    \/ (***************************************************************************)
       (* Some validator has claimed already, and now another validator makes a   *)
       (* non-conflicting claim                                                   *)
       (***************************************************************************)
       /\ phase = "AwaitingConsensus"
       /\ hasClaim = TRUE
       /\ UNCHANGED << phase, inputAccumulationPeriodOver, challengePeriodOver, epochIsSealed, hasClaim >>
    \/ (***************************************************************************)
       (* Some validator has claimed already, and now another validator makes a   *)
       (* conflicting claim, which initiates a dispute                            *)
       (***************************************************************************)
       /\ phase = "AwaitingConsensus"
       /\ hasClaim = TRUE
       /\ phase' = "AwaitingDispute"
       /\ UNCHANGED << inputAccumulationPeriodOver, challengePeriodOver, epochIsSealed, hasClaim >>

ResolveDispute ==
    \/ (***************************************************************************)
       (* Dispute is resolved before challenge period is over, and so we await    *)
       (* for consensus from the rest of the validators                           *)
       (***************************************************************************)
       /\ phase = "AwaitingDispute"
       /\ challengePeriodOver = FALSE
       /\ phase' = "AwaitingConsensus"
       /\ UNCHANGED << inputAccumulationPeriodOver, challengePeriodOver, epochIsSealed, hasClaim >>
    \/ (***************************************************************************)
       (* Dispute is resolved after challenge period is over, and so we go        *)
       (* directly towards the input accumulation period                          *)
       (***************************************************************************)
       /\ phase = "AwaitingDispute"
       /\ challengePeriodOver = TRUE
       /\ phase' = "InputAccumulation"
       /\ inputAccumulationPeriodOver' = FALSE
       /\ challengePeriodOver' = FALSE
       /\ hasClaim' = FALSE
       /\ epochIsSealed' = FALSE

FinalizeEpoch ==
    /\ phase = "AwaitingConsensus"
    /\ challengePeriodOver = TRUE
    /\ hasClaim = TRUE
    /\ phase' = "InputAccumulation"
    /\ inputAccumulationPeriodOver' = FALSE
    /\ challengePeriodOver' = FALSE
    /\ hasClaim' = FALSE
    /\ epochIsSealed' = FALSE

Next ==
    \/ EndInputAccumulationPeriod
    \/ EndChallengePeriod
    \/ AddInput
    \/ Claim
    \/ ResolveDispute
    \/ FinalizeEpoch

=============================================================================
\* Modification History
\* Last modified Wed Jun 08 16:24:36 BRT 2022 by guilherme
\* Created Wed Jun 01 09:08:33 BRT 2022 by guilherme
