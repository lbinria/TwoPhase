--------------------------- MODULE TwoPhaseTrace ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags, Json, IOUtils

(* Matches the configuration of the app. *)
\*CONSTANTS RM

JsonTracePath == IF "TRACE_PATH" \in DOMAIN IOEnv THEN IOEnv.TRACE_PATH ELSE "trace_unvalid_0.ndjson"

(* Read trace *)
JsonTrace ==
    ndJsonDeserialize(JsonTracePath)

(* Replace RM constant *)
RM ==
    JsonTrace[1].RM

(* Get trace skipping config line *)
Trace ==
    SubSeq(JsonTrace, 2, Len(JsonTrace))

(* Operators to apply when updating variable *)
(* signature: [string, any] *)
ExceptAt(var, arg, val) == [var EXCEPT ![arg] = val]
(* signature: [any] *)
AddElement(var, val) == var \cup {val}
(* signature: [any] *)
Replace(var, val) == val   \* 1st argument unnecessary but added for consistency

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
        IF "rmState" \in DOMAIN t
        THEN rmState' = Apply(rmState, t.rmState.op, t.rmState.args)
        ELSE TRUE
    /\
        IF "tmState" \in DOMAIN t
        THEN tmState' = Apply(tmState, t.tmState.op, t.tmState.args)
        ELSE TRUE
    /\
        IF "tmPrepared" \in DOMAIN t
        THEN tmPrepared' = Apply(tmPrepared, t.tmPrepared.op, t.tmPrepared.args)
        ELSE TRUE
    (* /\ "tmPrepared" \in DOMAIN t => tmPrepared' = Apply(tmPrepared, t.tmPrepared.op, t.tmPrepared.args) *)
    /\
        IF "msgs" \in DOMAIN t
        THEN msgs' = Apply(msgs, t.msgs.op, t.msgs.args)
        ELSE TRUE

ReadNext ==
    /\ i <= Len(Trace)
    /\ i' = i + 1
    /\ MapVariables(Trace[i])

-----------------------------------------------------------------------------

(* Infinite stuttering... *)
term ==
    /\ i > Len(Trace)
    /\ UNCHANGED vars

TPNext ==
    \/
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