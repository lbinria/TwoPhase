--------------------------- MODULE TwoPhaseTrace ---------------------------
(***************************************************************************)
(* Simplified specification of 2PC *)
(***************************************************************************)

EXTENDS TLC, Sequences, Naturals, FiniteSets

(* Matches the configuration of the app. *)
(* This can be generated via templating *)
(* Need configuration to be fixed *)
RM == {"rm1", "rm2"}


(* Handmade simple valid trace. *)
Trace_valid_1_0 == <<
    (* Trace r1 and r2 are working: some rmState changed *)
    (*
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "working" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "working" ],
    *)
    (* Trace r1 was prepared *)
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "prepared" ],
    [ op |-> "a", sender |-> "rm1", key |-> "msgs", val |-> "Prepared" ],
    [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm1" ],
    
    (* Trace r2 was prepared *)
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared" ],
    [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ],
    [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm2" ],
    (* Trace *)
    [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Commit" ],
    (* [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Abort" ], *)
    [ op |-> "w", sender |-> "TM", key |-> "tmState", val |-> "done" ]
>>

(* Handmade simple valid trace. *)
Trace_valid_1_1 == <<
    (* Trace rm1 and rm2 are working: some rmState changed *)
    (*
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "working" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "working" ],
    *)
    (* Trace rm1 was prepared *)
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "prepared" ],
    [ op |-> "a", sender |-> "rm1", key |-> "msgs", val |-> "Prepared" ],
    [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm1" ],
    
    (* Trace tm decide to abort *)
    [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Abort" ],
    [ op |-> "w", sender |-> "TM", key |-> "tmState", val |-> "done" ]
>>

(* Handmade simple valid trace. *)
Trace_valid_1_2 == <<
    (* Trace rm1 and rm2 are working: some rmState changed *)
    (*
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "working" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "working" ],
    *)
    (* Trace rm2 was prepared *)
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared" ],
    [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ],
    [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm2" ],
    
    (* Trace rm1 was aborted *)
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "aborted" ],
    
    (* Trace tm decide to abort (two lines of log below are not necessary to have a valid trace) *)
    [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Abort" ],
    [ op |-> "w", sender |-> "TM", key |-> "tmState", val |-> "done" ]
>>

(* Handmade simple unvalid trace. *)
(* But it is invalid because of :
    
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "aborted" ],
    [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ],

This log doesn't violate the 2PC protocol.d  
*)
Trace_unvalid_1_0 == <<
    (* Trace r1 and r2 are working: some rmState changed *)
    (*
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "working" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "working" ],
    *)
    (* Trace r2 was prepared *)
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared" ],
    (* Trace r1 was aborted *)
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "aborted" ],
    (* Trace r2 was prepared (next traces) *)
    [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ],
    [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm2" ],
    (* Trace *)
    [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Commit" ],
    [ op |-> "w", sender |-> "TM", key |-> "tmState", val |-> "done" ]
>>

(* Handmade simple unvalid trace. *)
Trace_unvalid_1_1 == <<
    (* Trace r1 and r2 are working: some rmState changed *)
    (*
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "working" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "working" ],
    *)
    (* Trace r2 was prepared *)
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared" ],
    [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ],
    (* Trace r1 was aborted *)
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "aborted" ],
    (* Trace r2 was prepared (next traces) *)
    [ op |-> "a", sender |-> "TM", key |-> "tmPrepared", val |-> "rm2" ],
    (* Trace *)
    [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Commit" ],
    [ op |-> "w", sender |-> "TM", key |-> "tmState", val |-> "done" ]
>>

(* Handmade simple unvalid trace. *)
Trace_unvalid_2_0 == <<
    (* Trace r1 and r2 are working: some rmState changed *)
    (*
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "working" ],
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "working" ],
    *)
    (* Trace r2 was prepared *)
    [ op |-> "w", sender |-> "rm2", key |-> "rmState", val |-> "prepared" ],
    (* Trace r1 was aborted *)
    [ op |-> "w", sender |-> "rm1", key |-> "rmState", val |-> "aborted" ],
    (* Trace r2 was prepared (next traces) *)
    [ op |-> "a", sender |-> "rm2", key |-> "msgs", val |-> "Prepared" ],
    (* Trace *)
    [ op |-> "a", sender |-> "TM", key |-> "msgs", val |-> "Commit" ],
    [ op |-> "w", sender |-> "TM", key |-> "tmState", val |-> "done" ]
>>

Trace == Trace_unvalid_1_0

\* INSTANCE IOUtils

\* Trace == IODeserialize("app-123.bin", TRUE)

VARIABLES
  rmState,       \* rmState[r] is the state of resource manager r.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
  msgs,          \* messages.
  i
  
vars == <<rmState, tmState, tmPrepared, msgs, i>>

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the RM indicated by the message's rm field to the TM.       *)
  (* Messages of type "Commit" and "Abort" are broadcast by the TM, to be  *)
  (* received by all RMs.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
  
TPInit == 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ i = 1
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
tmRcvPrepared(r) ==
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 1
  (* Expected trace *)
  /\ Trace[i].op = "a"
  /\ Trace[i].sender = "TM"
  /\ Trace[i].key = "tmPrepared"
  /\ Trace[i].val = r
  
  (* Sync predicate *)
  /\ tmPrepared' = tmPrepared \cup {r} \* sync with previous line
  /\ UNCHANGED <<rmState, tmState, msgs>>

tmCommit ==
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 2
  (* Expected trace (take account of order) *)
  /\ Trace[i].op = "a"
  /\ Trace[i].sender = "TM"
  /\ Trace[i].key = "msgs"
  /\ Trace[i].val = "Commit"

  /\ Trace[i + 1].op = "w"
  /\ Trace[i + 1].sender = "TM"
  /\ Trace[i + 1].key = "tmState"
  /\ Trace[i + 1].val = "done"
  

  
  (* Sync predicate *)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

tmAbort ==
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 2
  (* Expected trace (taking account of order) *)
  /\ Trace[i].op = "a"
  /\ Trace[i].sender = "TM"
  /\ Trace[i].key = "msgs"
  /\ Trace[i].val = "Abort"
  
  /\ Trace[i + 1].op = "w"
  /\ Trace[i + 1].sender = "TM"
  /\ Trace[i + 1].key = "tmState"
  /\ Trace[i + 1].val = "done"
  
  (* Sync predicate *)
  /\ tmState = "init"
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

rmPrepare(r) == 
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 2
  (* Expected trace (take account of order) *)
  /\ Trace[i].op = "w"
  /\ Trace[i].sender = r
  /\ Trace[i].key = "rmState"
  /\ Trace[i].val = "prepared"
  
  (* NOt really true that send message Prepared follow prepared, because, we can receive a message of another rm between the variable rmState is setted *)
  (* and the message is sent. We add to have a step to control that. **)
  /\ Trace[i + 1].op = "a"
  /\ Trace[i + 1].sender = r
  /\ Trace[i + 1].key = "msgs"
  /\ Trace[i + 1].val = "Prepared"
  
  (* Sync predicate *)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  
rmChooseToAbort(r) ==
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 1
  (* Expected trace *)
  /\ Trace[i].op = "w"
  /\ Trace[i].sender = r
  /\ Trace[i].key = "rmState"
  /\ Trace[i].val = "aborted"
  
  (* Sync predicate *)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

rmRcvCommitMsg(r) ==
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 1
  (* Expected trace *)
  /\ Trace[i].op = "w"
  /\ Trace[i].sender = r
  /\ Trace[i].key = "rmState"
  /\ Trace[i].val = "committed"
  
  (* Sync predicate *)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

rmRcvAbortMsg(r) ==
  (* Technical purposes *)
  /\ i <= Len(Trace)
  /\ i' = i + 1
  (* Expected trace *)
  /\ Trace[i].op = "w"
  /\ Trace[i].sender = r
  /\ Trace[i].key = "rmState"
  /\ Trace[i].val = "aborted"
  
  (* Sync predicate *)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
  

(* Infinite stuttering... *)
term == /\ i > Len(Trace)
        /\ UNCHANGED vars


       
TPNext ==
  \/ term
  \/ tmCommit \/ tmAbort
  \/ \E r \in RM : 
       tmRcvPrepared(r) \/ rmPrepare(r) \/ rmChooseToAbort(r)
         \/ rmRcvCommitMsg(r) \/ rmRcvAbortMsg(r)
         

TPTraceBehavior == TPInit /\ [][TPNext]_vars /\ WF_vars(TPNext)

Complete == <>[](i = Len(Trace) + 1)

TP == INSTANCE TwoPhase

(* No Deadlock *)
\* Invariant == waitSet # (Producers \cup Consumers)

THEOREM TPTraceBehavior => TP!TPSpec

(* BQInv == BQ!Invariant *)
TPSpec == TP!TPSpec
-----------------------------------------------------------------------------

(*
kSubsets(S, k) == IF S = {}
                  THEN {{}} \* kSubset of the empty set is the empty set.
                  ELSE { s \in SUBSET S : Cardinality(s) = k}

VARIABLES buffer, waitSet, i
vars == <<buffer, waitSet, i>>

Init == /\ i = 1
        /\ waitSet = {}
        /\ buffer = <<>>

Init == /\ buffer = <<>>
        /\ waitSet = {}

waitP == /\ i <= Len(Trace)
         /\ i' = i + 1
         /\ Trace[i].op = "w"
         /\ Trace[i].waiter = "p"
         (* The trace is incomplete because the App does not log the actual thread  *)
         (* that waits (the log only contains weather it is a consumer or producer).*)
         (* Thus, we select a running producer and add it to waitSet.               *)
         /\ waitSet' \in { waitSet \cup {t} : t \in (Producers \ waitSet) }
         /\ UNCHANGED buffer

waitC == /\ i <= Len(Trace)
         /\ i' = i + 1
         /\ Trace[i].op = "w"
         /\ Trace[i].waiter = "c"
         /\ waitSet' \in { waitSet \cup {t} : t \in (Consumers \ waitSet) }
         /\ UNCHANGED buffer

Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>

put == /\ i <= Len(Trace)
       /\ i' = i + 1
       /\ Trace[i].op = "e"
       (* The trace is incomplete because the App does not log which thread gets *)
       (* notified. Thus, we here notify a thread non-deterministically (the     *)
       (* same happens below in get).                                            *)
       /\ waitSet' \in kSubsets(waitSet, Cardinality(waitSet) - 1)
       (* The trace is also incomplete with regards to the buffer. Thus, we non- *)
       (* deterministically append an element to the buffer (again same below).  *)
       (* Note that only non-waiting producers can append.                       *)
       /\ buffer' \in { Append(buffer, e) : e \in (Producers \ waitSet) }
       
Put(t, d) ==
/\ t \notin waitSet
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(Consumers)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
       
get == /\ i <= Len(Trace)
       /\ i' = i + 1
       /\ Trace[i].op = "d"
       /\ waitSet' \in kSubsets(waitSet, Cardinality(waitSet) - 1)
       /\ buffer # <<>>
       /\ buffer' = Tail(buffer)
      
Get(t) ==
/\ t \notin waitSet
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(Producers)
   \/ /\ buffer = <<>>
      /\ Wait(t)
       
(* Infinite stuttering... *)
term == /\ i > Len(Trace)
        /\ UNCHANGED vars
               
Next == \/ waitP
        \/ waitC
        \/ put
        \/ get
        \/ term          

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

-----------------------------------------------------------------------------

TraceBehavior == Init /\ [][Next]_vars /\ WF_vars(Next)

Complete == <>[](i = Len(Trace) + 1)

BQ == INSTANCE BlockingQueue

THEOREM TraceBehavior => BQ!Invariant

BQInv == BQ!Invariant
BQSpec == BQ!Spec
*)

=============================================================================
\* Modification History
\* Last modified Fri Feb 03 19:47:02 CET 2023 by me
\* Created Fri Feb 03 10:18:07 CET 2023 by me
