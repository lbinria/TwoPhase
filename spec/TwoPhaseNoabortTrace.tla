---- MODULE TwoPhaseNoabortTrace ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, TwoPhaseNoabort, TVOperators, TraceSpec

vars == <<rmState, tmState, tmPrepared, msgs>>

(* Override CONSTANTS *)

(* Replace Nil constant *)
TraceNil == "null"

(* Replace RM constant *)
TraceRM ==
    ToSet(JsonTrace[1].RM)

(* Can be extracted from init *)
TPDefault(varName) ==
    CASE varName = "rmState" -> [r \in RM |-> "working"]
    []  varName = "tmState" -> "init"
    []  varName = "tmPrepared" -> {}
    []  varName = "msgs" -> {}

TPMapVariables(t) ==
    /\
        IF "rmState" \in DOMAIN t
        THEN rmState' = MapVariable(rmState, "rmState", t)
        ELSE TRUE
    /\
        IF "tmState" \in DOMAIN t
        THEN tmState' = MapVariable(tmState, "tmState", t)
        ELSE TRUE
    /\
        IF "tmPrepared" \in DOMAIN t
        THEN tmPrepared' = MapVariable(tmPrepared, "tmPrepared", t)
        ELSE TRUE
    /\
        IF "msgs" \in DOMAIN t
        THEN msgs' = MapVariable(msgs, "msgs", t)
        ELSE TRUE



IsTMCommit ==
    /\ IsEvent("TMCommit")
    /\ TMCommit

IsTMReset ==
    /\ IsEvent("TMReset")
    /\ TMReset

IsTMRcvPrepared ==
    /\ IsEvent("TMRcvPrepared")
    /\ \E r \in RM : TMRcvPrepared(r)

IsRMPrepare ==
    /\ IsEvent("RMPrepare")
    /\
        IF "event_args" \in DOMAIN logline /\ Len(logline.event_args) >= 1 THEN
            RMPrepare(logline.event_args[1])
        ELSE
            \E r \in RM : RMPrepare(r)

IsRMRcvCommitMsg ==
    /\ IsEvent("RMRcvCommitMsg")
    /\ \E r \in RM : RMRcvCommitMsg(r)

IsRMReset ==
    /\ IsEvent("RMReset")
    /\ \E r \in RM : RMReset(r)

TPTraceNext ==
        \/ IsTMCommit
        \/ IsTMReset
        \/ IsTMRcvPrepared
        \/ IsRMPrepare
        \/ IsRMRcvCommitMsg
        \/ IsRMReset


ComposedNext == FALSE

BASE == INSTANCE TwoPhase
BaseSpec == BASE!TPInit /\ [][BASE!TPNext \/ ComposedNext]_vars
====
