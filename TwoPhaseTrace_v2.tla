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
    [ sender |-> "rm2", action |->
        <<
            [key |-> "rmState", val |-> "prepared"],
            [key |-> "msgs", val |-> "Prepared"]
        >>
    ],
    (* Trace rm1 was prepared *)
    [ sender |-> "rm1", action |-> << [key |-> "rmState", val |-> "prepared"], [key |-> "msgs", val |-> "Prepared"] >>],
    [ sender |-> "TM", action |-> << [key |-> "tmPrepared", val |-> "rm1"] >>],
    [ sender |-> "TM", action |-> << [key |-> "tmPrepared", val |-> "rm2"] >>],
    [ sender |-> "TM", action |-> << [key |-> "msgs", val |-> "Commit"], [key |-> "tmState", val |-> "done"] >>]
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

(* Handmade simple valid trace. But doesn't work because the trace doesn't start after init state *)
Trace_valid_abort_2 == <<
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


MapRmState(t, a) ==
    /\ t.action[a].key = "rmState"
    /\ rmState' = [rmState EXCEPT ![t.sender] = t.action[a].val]

MapTmState(t, a) ==
    /\ t.action[a].key = "tmState"
    /\ tmState' = t.action[a].val

MapTmPrepared(t, a) ==
    /\ t.action[a].key = "tmPrepared"
    /\ tmPrepared' = tmPrepared \cup {t.action[a].val}

MapMsgs(t, a) ==
    /\ t.action[a].key = "msgs"
    /\
        \/
            /\ t.sender = "TM"
            /\ msgs' = msgs \cup {[type |-> t.action[a].val]}
        \/
            /\ t.sender # "TM"
            /\ msgs' = msgs \cup {[type |-> t.action[a].val, rm |-> t.sender]}


Map1Var(t) ==
    \/
        /\ MapRmState(t, 1)
        /\ UNCHANGED <<tmState, tmPrepared, msgs>>
    \/
        /\ MapTmState(t, 1)
        /\ UNCHANGED <<rmState, tmPrepared, msgs>>
    \/
        /\ MapTmPrepared(t, 1)
        /\ UNCHANGED <<rmState, tmState, msgs>>
    \/
        /\ MapMsgs(t, 1)
        /\ UNCHANGED <<rmState, tmState, tmPrepared>>

Map2Var(t) ==
    (* {rmState, tmState}, {rmState, tmPrepared}, {rmState, msgs}, {tmState, tmPrepared}, {tmState, msgs}, {tmPrepared, msgs} *)
    \/
        /\ \E a, b \in 1..2 : (MapRmState(t, a) /\ MapTmState(t, b) /\ a # b)
        /\ UNCHANGED <<tmPrepared, msgs>>
    \/
        /\ \E a, b \in 1..2 : (MapRmState(t, a) /\ MapTmPrepared(t, b) /\ a # b)
        /\ UNCHANGED <<tmState, msgs>>
    \/
        /\ \E a, b \in 1..2 : (MapRmState(t, a) /\ MapMsgs(t, b) /\ a # b)
        /\ UNCHANGED <<tmState, tmPrepared>>
    \/
        /\ \E a, b \in 1..2 : (MapTmState(t, a) /\ MapTmPrepared(t, b) /\ a # b)
        /\ UNCHANGED <<rmState, msgs>>
    \/
        /\ \E a, b \in 1..2 : (MapTmState(t, a) /\ MapMsgs(t, b) /\ a # b)
        /\ UNCHANGED <<rmState, tmPrepared>>
    \/
        /\ \E a, b \in 1..2 : MapTmPrepared(t, a) /\ MapMsgs(t, b) /\ a # b
        /\ UNCHANGED <<rmState, tmState>>

Map3Var(t) ==
    (* {rmState, tmState, tmPrepared}, {rmState, tmPrepared, msgs}, {tmState, tmPrepared, msgs} *)
    \/
        /\ \E a, b, c \in 1..3 : (MapRmState(t, a) /\ MapTmState(t, b) /\ MapTmPrepared(t, c) /\ a # b /\ a # c /\ b # c)
        /\ UNCHANGED <<msgs>>
    \/
        /\ \E a, b, c \in 1..3 : (MapRmState(t, a) /\ MapTmState(t, b) /\ MapMsgs(t, c) /\ a # b /\ a # c /\ b # c)
        /\ UNCHANGED <<tmPrepared>>
    \/
        /\ \E a, b, c \in 1..3 : (MapTmState(t, a) /\ MapTmPrepared(t, b) /\ MapMsgs(t, c) /\ a # b /\ a # c /\ b # c)
        /\ UNCHANGED <<rmState>>

MapAll(t) ==
    /\ \E a, b, c, d \in 1..4 :
        (MapRmState(t, a)
        /\ MapTmState(t, b)
        /\ MapTmPrepared(t, c)
        /\ MapMsgs(t, d)
        /\ a # b /\ a # c /\ a # d /\ b # c /\ b # d /\ c # d)

MapNothing == /\ UNCHANGED <<tmState, rmState, msgs, tmPrepared>>

(* Map log to TLA+ variables *)
MapVariable(t) ==
    IF Len(t.action) > 3 THEN
        MapAll(t)
    ELSE IF Len(t.action) = 3 THEN
        Map3Var(t)
    ELSE IF Len(t.action) = 2 THEN
        Map2Var(t)
    ELSE IF Len(t.action) = 1 THEN
        Map1Var(t)
    ELSE
        MapNothing

ReadNext == 
    /\ i <= Len(Trace)
    /\ i' = i + 1
    /\ MapVariable(Trace[i])

-----------------------------------------------------------------------------

(* Infinite stuttering... *)
term == /\ i > Len(Trace)
        /\ UNCHANGED vars

(*
TPNext ==
  \/
    (* UNCHANGED to accept some arbitrary log between interresting log *)
    (* but UNCHANGED can lead to accept deadlock ? *)
    /\ (TP!TPNext \/ UNCHANGED <<tmState, rmState, msgs, tmPrepared>>)
    /\ ReadNext
  \/
    /\ term
*)

TPNext ==
    \/
        (* Log and system are TRUE case *)
        (* /\ [TP!TPNext]_vars *)
        /\ [TP!TPNext]_vars
        /\ ReadNext

        (* Skip log case *)
        (* /\ ReadNext *)
        (* /\ UNCHANGED <<tmState, rmState, msgs, tmPrepared>> *)
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