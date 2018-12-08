----------------------------- MODULE messaging -----------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Readers, Writers, Topics, MaxQueueLen, Data

CONSTANT NULL

SeqOf(set, n) == UNION {[1..m -> set]: m \in 0..n}
seq (+) elt == Append(seq, elt)

set ++ set2 == set \union set2
Messages == [source: Writers, msg: Data]

(*--algorithm messaging
variable
  queues = [r \in Readers |-> <<>>], 
  subscribed = [t \in Topics |-> {}];
  
define
TypeInvariant ==
  /\ queues \in [Readers -> SeqOf(Messages, MaxQueueLen)]
  /\ subscribed \in [Topics -> SUBSET Readers]
end define

process reader \in Readers
variable local = NULL;
begin
Read:
while TRUE do
  either \* receive
    await Len(queues[self]) > 0;
    either \* read something off the queue
      local := Head(queues[self]);
    or
      local := NULL;
    end either;  
    \* the queueing service knows you've taken the thing off the queue regardless
    \* of if you actually got it.
    queues[self] := Tail(queues[self]);
  or \* subscribe
    with t \in Topics do
      await self \notin subscribed[t];
      subscribed[t] := subscribed[t] ++ {self};
    end with;
  or \* unsubscribe
    with t \in Topics do
      await self \in subscribed[t];
      subscribed[t] := subscribed[t] \ {self};
    end with;
  end either;
end while;
end process;

process writer \in Writers
begin
Write:
while TRUE do
  with t \in Topics do
    await subscribed[t] /= {};
    with msg \in Data do
      queues := [r \in subscribed[t] |-> queues[r] (+) [source |-> self, msg |-> msg]] @@ queues; 
    end with;
  end with;
end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES queues, subscribed

(* define statement *)
TypeInvariant ==
  /\ queues \in [Readers -> SeqOf(Messages, MaxQueueLen)]
  /\ subscribed \in [Topics -> SUBSET Readers]

VARIABLE local

vars == << queues, subscribed, local >>

ProcSet == (Readers) \cup (Writers)

Init == (* Global variables *)
        /\ queues = [r \in Readers |-> <<>>]
        /\ subscribed = [t \in Topics |-> {}]
        (* Process reader *)
        /\ local = [self \in Readers |-> NULL]

reader(self) == \/ /\ Len(queues[self]) > 0
                   /\ \/ /\ local' = [local EXCEPT ![self] = Head(queues[self])]
                      \/ /\ local' = [local EXCEPT ![self] = NULL]
                   /\ queues' = [queues EXCEPT ![self] = Tail(queues[self])]
                   /\ UNCHANGED subscribed
                \/ /\ \E t \in Topics:
                        /\ self \notin subscribed[t]
                        /\ subscribed' = [subscribed EXCEPT ![t] = subscribed[t] ++ {self}]
                   /\ UNCHANGED <<queues, local>>
                \/ /\ \E t \in Topics:
                        /\ self \in subscribed[t]
                        /\ subscribed' = [subscribed EXCEPT ![t] = subscribed[t] \ {self}]
                   /\ UNCHANGED <<queues, local>>

writer(self) == /\ \E t \in Topics:
                     /\ subscribed[t] /= {}
                     /\ \E msg \in Data:
                          queues' = [r \in subscribed[t] |-> queues[r] (+) [source |-> self, msg |-> msg]] @@ queues
                /\ UNCHANGED << subscribed, local >>

Next == (\E self \in Readers: reader(self))
           \/ (\E self \in Writers: writer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Dec 08 14:08:38 EST 2018 by john
\* Created Fri Dec 07 16:51:47 EST 2018 by john
