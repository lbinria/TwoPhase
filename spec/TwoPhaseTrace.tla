--------------------------- MODULE TwoPhaseTrace ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, TwoPhase, TVOperators, TraceSpec

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
        THEN rmState' = ApplyUpdates(rmState, "rmState", t.rmState)
        ELSE TRUE
    /\
        IF "tmState" \in DOMAIN t
        THEN tmState' = ApplyUpdates(tmState, "tmState", t.tmState)
        ELSE TRUE
    /\
        IF "tmPrepared" \in DOMAIN t
        THEN tmPrepared' = ApplyUpdates(tmPrepared, "tmPrepared", t.tmPrepared)
        ELSE TRUE
    /\
        IF "msgs" \in DOMAIN t
        THEN msgs' = ApplyUpdates(msgs, "msgs", t.msgs)
        ELSE TRUE



IsTMCommit ==
    /\ IsEvent("TMCommit")
    /\ TMCommit

IsTMAbort ==
    /\ IsEvent("TMAbort")
    /\ TMAbort

IsTMReset ==
    /\ IsEvent("TMReset")
    /\ TMReset

IsTMRcvPrepared ==
    /\ IsEvent("TMRcvPrepared")
    /\ \E r \in RM : TMRcvPrepared(r)

IsRMPrepare ==
    /\ IsEvent("RMPrepare")
    /\ \E r \in RM : RMPrepare(r)

IsRMChooseToAbort ==
    /\ IsEvent("RMChooseToAbort")
    /\ \E r \in RM : RMChooseToAbort(r)

IsRMRcvCommitMsg ==
    /\ IsEvent("RMRcvCommitMsg")
    /\ \E r \in RM : RMRcvCommitMsg(r)

IsRMRcvAbortMsg ==
    /\ IsEvent("RMRcvAbortMsg")
    /\ \E r \in RM : RMRcvAbortMsg(r)

IsRMReset ==
    /\ IsEvent("RMReset")
    /\ \E r \in RM : RMReset(r)

TPTraceNext ==
        \/ IsTMCommit
        \/ IsTMAbort
        \/ IsTMReset
        \/ IsTMRcvPrepared
        \/ IsRMPrepare
        \/ IsRMChooseToAbort
        \/ IsRMRcvCommitMsg
        \/ IsRMRcvAbortMsg
        \/ IsRMReset


ComposedNext == TRUE

BASE == INSTANCE TwoPhase
BaseSpec == BASE!TPInit /\ [][BASE!TPNext \/ ComposedNext]_vars
-----------------------------------------------------------------------------
=============================================================================