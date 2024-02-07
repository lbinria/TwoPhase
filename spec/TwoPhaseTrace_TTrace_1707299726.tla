---- MODULE TwoPhaseTrace_TTrace_1707299726 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, TwoPhaseTrace

_expression ==
    LET TwoPhaseTrace_TEExpression == INSTANCE TwoPhaseTrace_TEExpression
    IN TwoPhaseTrace_TEExpression!expression
----

_trace ==
    LET TwoPhaseTrace_TETrace == INSTANCE TwoPhaseTrace_TETrace
    IN TwoPhaseTrace_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        msgs = ({[type |-> "Abort"]})
        /\
        tmState = ("done")
        /\
        tmPrepared = ({})
        /\
        rmState = (("rm-0" :> "working" @@ "rm-1" :> "working"))
        /\
        l = (4)
    )
----

_init ==
    /\ l = _TETrace[1].l
    /\ tmPrepared = _TETrace[1].tmPrepared
    /\ msgs = _TETrace[1].msgs
    /\ rmState = _TETrace[1].rmState
    /\ tmState = _TETrace[1].tmState
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ l  = _TETrace[i].l
        /\ l' = _TETrace[j].l
        /\ tmPrepared  = _TETrace[i].tmPrepared
        /\ tmPrepared' = _TETrace[j].tmPrepared
        /\ msgs  = _TETrace[i].msgs
        /\ msgs' = _TETrace[j].msgs
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState
        /\ tmState  = _TETrace[i].tmState
        /\ tmState' = _TETrace[j].tmState

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TwoPhaseTrace_TTrace_1707299726.json", _TETrace)

=============================================================================

 Note that you can extract this module `TwoPhaseTrace_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TwoPhaseTrace_TEExpression.tla` file takes precedence 
  over the module `TwoPhaseTrace_TEExpression` below).

---- MODULE TwoPhaseTrace_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, TwoPhaseTrace

expression == 
    [
        \* To hide variables of the `TwoPhaseTrace` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        l |-> l
        ,tmPrepared |-> tmPrepared
        ,msgs |-> msgs
        ,rmState |-> rmState
        ,tmState |-> tmState
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_lUnchanged |-> l = l'
        
        \* Format the `l` variable as Json value.
        \* ,_lJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(l)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_lModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].l # _TETrace[s-1].l
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE TwoPhaseTrace_TETrace ----
\*EXTENDS IOUtils, TLC, TwoPhaseTrace
\*
\*trace == IODeserialize("TwoPhaseTrace_TTrace_1707299726.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TwoPhaseTrace_TETrace ----
EXTENDS TLC, TwoPhaseTrace

trace == 
    <<
    ([msgs |-> {},tmState |-> "init",tmPrepared |-> {},rmState |-> ("rm-0" :> "working" @@ "rm-1" :> "working"),l |-> 1]),
    ([msgs |-> {},tmState |-> "init",tmPrepared |-> {},rmState |-> ("rm-0" :> "working" @@ "rm-1" :> "working"),l |-> 2]),
    ([msgs |-> {[type |-> "Abort"]},tmState |-> "done",tmPrepared |-> {},rmState |-> ("rm-0" :> "working" @@ "rm-1" :> "working"),l |-> 3]),
    ([msgs |-> {[type |-> "Abort"]},tmState |-> "done",tmPrepared |-> {},rmState |-> ("rm-0" :> "working" @@ "rm-1" :> "working"),l |-> 4])
    >>
----


=============================================================================

---- CONFIG TwoPhaseTrace_TTrace_1707299726 ----
CONSTANTS
    Nil <- TraceNil
    RM <- TraceRM
    Default <- TPDefault
    Vars <- vars
    BaseInit <- TPInit
    MapVariables <- TPMapVariables
    TraceNext <- TPTraceNext

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Feb 07 10:55:27 CET 2024