--------------------------- MODULE TwoPhaseTrace_v4 ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

(* Matches the configuration of the app. *)
(* This can be generated via templating *)
(* Need configuration to be fixed *)
CONSTANTS RM

(* Operators to apply when updating variable *)
Operators == [rmState |-> "fappend", tmState |-> "assign", tmPrepared |-> "union", msgs |-> "union"]
(* Types of variables *)
VarTypes == [rmState |-> "record", tmState |-> "singleton", tmPrepared |-> "set", msgs |-> "set"]

(* Handmade simple valid trace. *)
Trace_valid_commit == <<
    (* Trace rm2 was prepared *)
    [
        \* rmState |-> [rm2 |-> "prepared"],
        rmState |-> << "rm2", "prepared" >>,
        msgs |-> {[type |-> "Prepared", rm |-> "rm2"]}
    ],
    (* Trace rm1 was prepared *)
    [
        \* rmState |-> [rm1 |-> "prepared"],
        rmState |-> << "rm1", "prepared" >>,
        msgs |-> {[type |-> "Prepared", rm |-> "rm1"]}
    ],
    (* Trace tm add prepared *)
    [tmPrepared |-> {"rm1"}],
    [tmPrepared |-> {"rm2"}],
    [
        msgs |-> {[type |-> "Commit"]},
        tmState |-> "done"
    ]
>>

Trace == Trace_valid_commit

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

Apply(name, var, val) ==
    (* Assignment *)
    IF Operators[name] = "assign" THEN
        var' = val
    (* Function append *)
    ELSE IF Operators[name] = "fappend" THEN
        var' = [var EXCEPT ![val[1]] = val[2]]
    (* Set union *)
    ELSE IF Operators[name] = "union" THEN
        var' = var \cup val
    (* Set diff *)
    ELSE IF Operators[name] = "diff" THEN
        var' = var \ val
    (* Sequence add element *)
    ELSE IF Operators[name] = "sappend" THEN
        var' = var \o val
    (* Sequence remove element (TODO check if notin works with sequences <<>>) *)
    ELSE IF Operators[name] = "sremove" THEN
        var' = SelectSeq(var, LAMBDA x: x \notin val)
    (* Bag append *)
    ELSE IF Operators[name] = "bappend" THEN
        var' = var (+) val
    (* Bag remove *)
    ELSE IF Operators[name] = "bremove" THEN
        var' = var (-) val
    ELSE
        var' = var


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