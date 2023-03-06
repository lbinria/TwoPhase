--------------------------- MODULE TwoPhaseTrace ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

(* Matches the configuration of the app. *)
(* This can be generated via templating *)
(* Need configuration to be fixed *)
CONSTANTS RM

(* Operators to apply when updating variable *)
(* signature: [string, any] *)
ExceptAt(var, arg, val) == [var EXCEPT ![arg] = val]
(* signature: [any] *)
AddElement(var, val) == var \cup {val}
(* signature: [any] *)
Replace(var, val) == val   \* 1st argument unnecessary but added for consistency

(* Handmade simple valid trace. *)
Trace_valid_commit == <<
    (* Trace rm2 was prepared *)
    [
        rmState |-> [op |-> "ExceptAt", args |-> <<"rm2", "prepared">>],
        msgs |-> [op |-> "AddElement", args |-> <<[type |-> "Prepared", rm |-> "rm2"]>>]
    ],
    (* Trace rm1 was prepared *)
    [
        rmState |-> [op |-> "ExceptAt", args |-> <<"rm1", "prepared">>],
        msgs |-> [op |-> "AddElement", args |-> <<[type |-> "Prepared", rm |-> "rm1"]>>]
    ],
    (* Trace tm add prepared *)
    [tmPrepared |-> [op |-> "AddElement", args |-> <<"rm1">>]],
    [tmPrepared |-> [op |-> "AddElement", args |-> <<"rm2">>]],
    [
        msgs |-> [op |-> "AddElement", args |-> <<[type |-> "Commit"]>>],
        tmState |-> [op |-> "Replace", args |-> <<"done">>]
    ]
>>

(* Handmade simple unvalid trace. *)
Trace_unvalid_0 == <<
    (* Trace rm2 was prepared *)
    [
        rmState |-> [op |-> "ExceptAt", args |-> <<"rm2", "prepared">>],
        msgs |-> [op |-> "AddElement", args |-> <<[type |-> "Prepared", rm |-> "rm2"]>>]
    ],
    (* Trace rm1 was prepared *)
    [
        rmState |-> [op |-> "ExceptAt", args |-> <<"rm1", "prepared">>],
        msgs |-> [op |-> "AddElement", args |-> <<[type |-> "Prepared", rm |-> "rm1"]>>]
    ],
    (* Trace tm add prepared *)
    [tmPrepared |-> [op |-> "AddElement", args |-> <<"rm1">>]],
    [tmPrepared |-> [op |-> "AddElement", args |-> <<"rm2">>]],
    [
        msgs |-> [op |-> "AddElement", args |-> <<[type |-> "Abort"]>>],
        tmState |-> [op |-> "Replace", args |-> <<"done">>]
    ],
    (* Trace rm1 was committed *)
    [
        rmState |-> [op |-> "ExceptAt", args |-> <<"rm1", "committed">>]
    ],
    (* Trace rm2 was aborted *)
    [
        rmState |-> [op |-> "ExceptAt", args |-> <<"rm1", "aborted">>]
    ]
>>

Word == "bob"

\* Trace == Trace_valid_commit
\*Trace == Trace_unvalid_0

INSTANCE IOUtils
Trace == IODeserialize("Trace.bin", TRUE)

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

Apply(var, op, args) ==
   CASE op = "ExceptAt" -> ExceptAt(var, args[1], args[2])
   []   op = "AddElement" -> AddElement(var, args[1])
   []   op = "Replace" -> Replace(var, args[1])


MapVariables(t) ==
    /\
        rmState' =
          IF "rmState" \in DOMAIN t
          THEN Apply(rmState, t.rmState.op, t.rmState.args)
          ELSE rmState
    /\
        tmState' =
          IF "tmState" \in DOMAIN t
          THEN Apply(tmState, t.tmState.op, t.tmState.args)
          ELSE tmState
    /\
        tmPrepared' =
          IF "tmPrepared" \in DOMAIN t
          THEN Apply(tmPrepared, t.tmPrepared.op, t.tmPrepared.args)
          ELSE tmPrepared
    /\
        msgs' =
          IF "msgs" \in DOMAIN t
          THEN Apply(msgs, t.msgs.op, t.msgs.args)
          ELSE msgs

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
        (* not ENABLED (ReadNext /\ TPNext) /\ TPNext /\ i' = i *)
        /\ ReadNext
        /\ [TP!TPNext]_vars
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