--------------------------- MODULE TwoPhaseTrace ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets

(* Matches the configuration of the app. *)
(* This can be generated via templating *)
(* Need configuration to be fixed *)
CONSTANTS RM


(* Handmade simple valid trace. *)
Trace_valid_commit == <<
    (* Trace rm2 was prepared *)
    <<
        [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared"],
        [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ]
    >>,
    (* Found log out of spec, shouldn't invalidate trace ... *)
    (* << [ op |-> "w", sender |-> "bob", key |-> "say", val |-> "hello !"] >>, *)
    (* Trace rm1 was prepared *)
    <<
        [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "prepared"],
        [ op |-> "a", sender |-> "rm1", key |-> "msgs", val |-> "Prepared" ]
    >>,
    << [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm1" ] >>,
    << [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm2" ] >>,
    <<
        [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Commit" ],
        [ op |-> "a", sender |-> "TM", key |-> "tmState", val |-> "done" ]
    >>

>>

(* Handmade simple valid trace. *)
Trace_valid_abort == <<
    (* Trace rm2 was prepared *)
    <<
        [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared"],
        [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ]
    >>,
    (* Found log out of spec, shouldn't invalidate trace ... *)
    << [ op |-> "w", sender |-> "bob", key |-> "say", val |-> "hello !"] >>,
    << [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm2" ] >>,
    (* Trace rm1 was prepared *)
    <<
        [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "prepared"],
        [ op |-> "a", sender |-> "rm1", key |-> "msgs", val |-> "Prepared" ]
    >>,
    << [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm1" ] >>,

    <<
        [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Abort" ],
        [ op |-> "a", sender |-> "TM", key |-> "tmState", val |-> "done" ]
    >>

>>

\* Trace == Trace_valid_abort

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

(* Map log to TLA+ variables *)
LogMap(t) ==
    (* The two state changes go together (see TwoPhase spec) see ordered or not ? ... *)
    IF Len(t) = 2 /\ t[1].key = "rmState" /\ t[2].key = "msgs" THEN
        /\ rmState' = [rmState EXCEPT ![t[1].sender] = t[1].val]
        /\ msgs' = msgs \cup {[type |-> t[2].val, rm |-> t[2].sender]}
        /\ UNCHANGED <<tmState, tmPrepared>>

    ELSE IF Len(t) = 1 /\ t[1].key = "tmState" THEN
        /\ tmState' = t[1].val
        /\ UNCHANGED <<rmState, tmPrepared, msgs>>

    ELSE IF Len(t) = 1 /\ t[1].key = "tmPrepared" THEN
        /\ tmPrepared' = tmPrepared \cup {t[1].val}
        /\ UNCHANGED <<tmState, rmState, msgs>>

    ELSE IF Len(t) = 2 /\ t[1].key = "msgs" /\ t[1].sender = "TM" /\ t[2].key = "tmState" THEN
        /\ msgs' = msgs \cup {[type |-> t[1].val]}
        /\ tmState' = t[2].val
        /\ UNCHANGED <<rmState, tmPrepared>>
    ELSE
        UNCHANGED <<tmState, rmState, msgs, tmPrepared>>

ReadNext == 
    /\ i <= Len(Trace)
    /\ i' = i + 1
    /\ LogMap(Trace[i])

-----------------------------------------------------------------------------

(* Infinite stuttering... *)
term == /\ i > Len(Trace)
        /\ UNCHANGED vars
       
TPNext ==
  \/
    (* UNCHANGED to accept some arbitrary log between interresting log *)
    (* but UNCHANGED can lead to accept deadlock ? *)
    /\ (TP!TPNext \/ UNCHANGED <<tmState, rmState, msgs, tmPrepared>>)
    /\ ReadNext
  \/
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