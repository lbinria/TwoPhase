--------------------------- MODULE TwoPhaseTraceConstraint ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, TwoPhase

ASSUME TLCGet("config").mode = "bfs"
vars == <<rmState, tmState, tmPrepared, msgs>>

(* Read trace *)
JsonTrace ==
    IF "TRACE_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.TRACE_PATH)
    ELSE
        Print(<<"Failed to validate the trace. TRACE_PATH environnement variable was expected.">>, "")

NoVal == "null"

(* Replace RM constant *)
TraceRM ==
    ToSet(JsonTrace[1].RM)

(* Get trace skipping config line *)
Trace ==
    SubSeq(JsonTrace, 2, Len(JsonTrace))

(* Generic operators *)
Replace(cur, val) == val
AddElement(cur, val) == cur \cup {val}
AddElements(cur, vals) == cur \cup ToSet(vals)
RemoveElement(cur, val) == cur \ {val}
Clear(cur, val) == {}
\*RemoveKey(cur, val) == NoVal
RemoveKey(cur, val) == [k \in DOMAIN cur |-> IF k = val THEN NoVal ELSE cur[k]]
UpdateRec(cur, val) == [k \in DOMAIN cur |-> IF k \in DOMAIN val THEN val[k] ELSE cur[k]]

(* Can be extracted from init *)
Default(varName) ==
    CASE varName = "rmState" -> [r \in RM |-> "working"]
    []  varName = "tmState" -> "init"
    []  varName = "tmPrepared" -> {}
    []  varName = "msgs" -> {}

Apply(var, default, op, args) ==
    CASE op = "Replace" -> Replace(var, args[1])
    []   op = "AddElement" -> AddElement(var, args[1])
    []   op = "AddElements" -> AddElements(var, args[1])
    []   op = "RemoveElement" -> RemoveElement(var, args[1])
    []   op = "Clear" -> Clear(var, <<>>)
    []   op = "RemoveKey" -> RemoveKey(var, args[1])
    []   op = "UpdateRec" -> UpdateRec(var, args[1])
    []   op = "Init" -> Replace(var, default)
    []   op = "InitWithValue" -> UpdateRec(default, args[1])

RECURSIVE ExceptAtPath(_,_,_,_,_)
LOCAL ExceptAtPath(var, default, path, op, args) ==
    LET h == Head(path) IN
    IF Len(path) > 1 THEN
        [var EXCEPT ![h] = ExceptAtPath(var[h], default[h], Tail(path), op, args)]
    ELSE
        [var EXCEPT ![h] = Apply(@, default[h], op, args)]

RECURSIVE ExceptAtPaths(_,_,_)
LOCAL ExceptAtPaths(var, varName, updates) ==
    LET update == Head(updates) IN

    LET applied ==
        IF Len(update.path) > 0 THEN
            ExceptAtPath(var, Default(varName), update.path, update.op, update.args)
        ELSE
            Apply(var, Default(varName), update.op, update.args)
    IN
    IF Len(updates) > 1 THEN
        ExceptAtPaths(applied, varName, Tail(updates))
    ELSE
        applied

TP == INSTANCE TwoPhase

TraceInit ==
    \* The implementation's initial state is deterministic and known.
    \* TLCGet("level") = 1 => /\ KV!Init
    TRUE

TraceSpec ==
    \* Because of  [A]_v <=> A \/ v=v'  , the following formula is logically
     \* equivalent to the (canonical) Spec formual  Init /\ [][Next]_vars  .
     \* However, TLC's breadth-first algorithm does not explore successor
     \* states of a *seen* state.  Since one or more states may appear one or
     \* more times in the the trace, the  UNCHANGED vars  combined with the
     \*  TraceView  that includes  TLCGet("level")  is our workaround.
    TraceInit /\ [][TPNext \/ UNCHANGED vars]_vars

MapVariables(t) ==
    /\
        IF "rmState" \in DOMAIN t
        THEN rmState' = ExceptAtPaths(rmState, "rmState", t.rmState)
        ELSE TRUE
    /\
        IF "tmState" \in DOMAIN t
        THEN tmState' = ExceptAtPaths(tmState, "tmState", t.tmState)
        ELSE TRUE
    /\
        IF "tmPrepared" \in DOMAIN t
        THEN tmPrepared' = ExceptAtPaths(tmPrepared, "tmPrepared", t.tmPrepared)
        ELSE TRUE
    /\
        IF "msgs" \in DOMAIN t
        THEN msgs' = ExceptAtPaths(msgs, "msgs", t.msgs)
        ELSE TRUE

TraceNextConstraint ==
    LET i == TLCGet("level")
    IN
        /\ i <= Len(Trace)
        /\ MapVariables(Trace[i])

TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(Trace) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", Trace[d],
                    "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

TraceView ==
    \* A high-level state  s  can appear multiple times in a system trace.  Including the
     \* current level in TLC's view ensures that TLC will not stop model checking when  s
     \* appears the second time in the trace.  Put differently,  TraceView  causes TLC to
     \* consider  s_i  and s_j  , where  i  and  j  are the positions of  s  in the trace,
     \* to be different states.
    <<vars, TLCGet("level")>>

-----------------------------------------------------------------------------
=============================================================================