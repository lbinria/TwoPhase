--------------------------- MODULE TwoPhaseTrace_v3 ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets

(* Matches the configuration of the app. *)
(* This can be generated via templating *)
(* Need configuration to be fixed *)
CONSTANTS RM

(* Complete assignment example *)

(* Handmade simple valid trace. *)
Trace_valid_commit == <<
    (* Trace rm2 was prepared *)
    [ sender |-> "rm2", action |->
        [
            rmState |-> [rm1 |-> "working", rm2 |-> "prepared"],
            msgs |-> {[type |-> "Prepared", rm |-> "rm2"]}
        ]
    ],
    (* Trace rm1 was prepared *)
    [ sender |-> "rm1", action |->
        [
            rmState |-> [rm1 |-> "prepared", rm2 |-> "prepared"],
            msgs |-> {[type |-> "Prepared", rm |-> "rm2"], [type |-> "Prepared", rm |-> "rm1"]}
        ]
    ],
    (* Trace tm add prepared *)
    [ sender |-> "TM", action |->
        [tmPrepared |-> {"rm1"}]
    ],
    [ sender |-> "TM", action |->
        [tmPrepared |-> {"rm1", "rm2"}]
    ],
    [ sender |-> "TM", action |->
        [
            msgs |-> {[type |-> "Prepared", rm |-> "rm2"], [type |-> "Prepared", rm |-> "rm1"], [type |-> "Commit"]},
            tmState |-> "done"
        ]
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

MapVariables(t) ==
    /\
        \/ "rmState" \notin DOMAIN t.action /\ rmState' = rmState
        \/ "rmState" \in DOMAIN t.action /\ rmState' = t.action.rmState
    /\
        \/ "tmState" \notin DOMAIN t.action /\ tmState' = tmState
        \/ "tmState" \in DOMAIN t.action /\ tmState' = t.action.tmState
    /\
        \/ "tmPrepared" \notin DOMAIN t.action /\ tmPrepared' = tmPrepared
        \/ "tmPrepared" \in DOMAIN t.action /\ tmPrepared' = t.action.tmPrepared
    /\
        \/ "msgs" \notin DOMAIN t.action /\ msgs' = msgs
        \/ "msgs" \in DOMAIN t.action /\ msgs' = t.action.msgs

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