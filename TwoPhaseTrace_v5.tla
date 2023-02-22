--------------------------- MODULE TwoPhaseTrace_v5 ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags


(* Matches the configuration of the app. *)
(* This can be generated via templating *)
(* Need configuration to be fixed *)
CONSTANTS RM

(* Operators to apply when updating variable *)
\* Operators == [rmState |-> "fappend", tmState |-> "assign", tmPrepared |-> "union", msgs |-> "union"]
(* Types of variables *)
VarTypes == [rmState |-> "record", tmState |-> "unstructured", tmPrepared |-> "set", msgs |-> "set"]
(* Instance apply module *)
INSTANCE Apply WITH VarTypes <- VarTypes

(* Handmade simple valid trace. *)
Trace_valid_commit == <<
    (* Trace rm2 was prepared *)
    [
        \* TODO is there a way to do that ?
        \* rmState |-> [op |-> "+", val |-> [ rm2 |-> "prepared"]],
        rmState |-> [op |-> "+", val |-> [ key |-> "rm2", val |-> "prepared"]],
        msgs |-> [op |-> "+", val |-> {[type |-> "Prepared", rm |-> "rm2"]}]
    ],
    (* Trace rm1 was prepared *)
    [
        \* TODO is there a way to do that ?
        \* rmState |-> [op |-> "+", val |-> [ rm1 |-> "prepared"]],
        rmState |-> [op |-> "+", val |-> [ key |-> "rm1", val |-> "prepared"]],
        msgs |-> [op |-> "+", val |-> {[type |-> "Prepared", rm |-> "rm1"]}]
    ],
    (* Trace tm add prepared *)
    [tmPrepared |-> [op |-> "+", val |-> {"rm1"}]],
    [tmPrepared |-> [op |-> "+", val |-> {"rm2"}]],
    [
        msgs |-> [op |-> "+", val |-> {[type |-> "Commit"]}],
        tmState |-> [op |-> "=", val |-> "done"]
    ]
>>

(* Handmade simple unvalid trace. *)
Trace_unvalid_0 == <<
    (* Trace rm2 was prepared *)
    [
        \* TODO is there a way to do that ?
        \* rmState |-> [op |-> "+", val |-> [ rm2 |-> "prepared"]],
        rmState |-> [op |-> "+", val |-> [ key |-> "rm2", val |-> "prepared"]],
        msgs |-> [op |-> "+", val |-> {[type |-> "Prepared", rm |-> "rm2"]}]
    ],
    (* Trace rm1 was prepared *)
    [
        \* TODO is there a way to do that ?
        \* rmState |-> [op |-> "+", val |-> [ rm1 |-> "prepared"]],
        rmState |-> [op |-> "+", val |-> [ key |-> "rm1", val |-> "prepared"]],
        msgs |-> [op |-> "+", val |-> {[type |-> "Prepared", rm |-> "rm1"]}]
    ],
    (* Trace tm add prepared *)
    [tmPrepared |-> [op |-> "+", val |-> {"rm1"}]],
    [tmPrepared |-> [op |-> "+", val |-> {"rm2"}]],
    [
        msgs |-> [op |-> "+", val |-> {[type |-> "Abort"]}],
        tmState |-> [op |-> "=", val |-> "done"]
    ],
    (* Trace rm1 was committed *)
    [
        \* TODO is there a way to do that ?
        \* rmState |-> [op |-> "+", val |-> [ rm1 |-> "committed"]],
        rmState |-> [op |-> "+", val |-> [ key |-> "rm1", val |-> "committed"]]
    ],
    (* Trace rm2 was aborted *)
    [
        \* TODO is there a way to do that ?
        \* rmState |-> [op |-> "+", val |-> [ rm1 |-> "aborted"]],
        rmState |-> [op |-> "+", val |-> [ key |-> "rm1", val |-> "aborted"]]
    ]
>>

\*Trace == Trace_valid_commit
Trace == Trace_unvalid_0

INSTANCE IOUtils
\* Trace == IODeserialize("Trace.bin", TRUE)

VARIABLES
  rmState,       \* rmState[r] is the state of resource manager r.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
  msgs,          \* messages.
  i

vars == <<rmState, tmState, tmPrepared, msgs, i>>

TP == INSTANCE TwoPhase

(* Can be generated *)
TPInit ==
  /\ i = 1
  /\ TP!TPInit

MapVariables(t) ==
    /\
        IF "rmState" \in DOMAIN t THEN
            Apply("rmState", rmState, t.rmState)
        ELSE
            rmState' = rmState
    /\
        IF "tmState" \in DOMAIN t THEN
            Apply("tmState", tmState, t.tmState)
        ELSE
            tmState' = tmState
    /\
        IF "tmPrepared" \in DOMAIN t THEN
            Apply("tmPrepared", tmPrepared, t.tmPrepared)
        ELSE
            tmPrepared' = tmPrepared
    /\
        IF "msgs" \in DOMAIN t THEN
            Apply("msgs", msgs, t.msgs)
        ELSE
            msgs' = msgs

ReadNext ==
    /\ i <= Len(Trace)
    /\ i' = i + 1
    /\ MapVariables(Trace[i])

-----------------------------------------------------------------------------

(* Infinite stuttering... *)
term == /\ i > Len(Trace)
        /\ UNCHANGED vars

TPNext ==
    \/
        (* Log and system are TRUE case *)
        (* or Skip log case *)
        /\ [TP!TPNext]_vars
        /\ ReadNext
    \/
        (* All trace processed case *)
        /\ term

TPTraceBehavior == TPInit /\ [][TPNext]_vars /\ WF_vars(TPNext)

Complete == <>[](i = Len(Trace) + 1)


THEOREM TPTraceBehavior => TP!TPSpec
THEOREM TPTraceBehavior => []TP!TPTypeOK

(* Property to check *)
TPSpec == TP!TPSpec
(* Invariant *)
TPTypeOK == TP!TPTypeOK
-----------------------------------------------------------------------------

=============================================================================