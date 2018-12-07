------------------------------- MODULE dekker -------------------------------
EXTENDS TLC, Integers, Sequences

Threads == {1, 2}
(*--algorithm dekker
variables flags = [t \in Threads |-> FALSE], next_thread \in Threads;

procedure thread()
begin
  P1: flags[self] := TRUE;
  P2:
      while \E t \in Threads \ {self}: flags[t] do
          P2_1:
              if next_thread /= self then
                  P2_1_1: flags[self] := FALSE;
                  P2_1_2: await next_thread = self;
                  P2_1_3: flags[self] := TRUE;
              end if;
      end while; 
  CS: skip;
  P3: with thread \in Threads \ {self} do
          next_thread := thread;
      end with;
  P4: flags[self] := FALSE;
  P5: goto P1;
end procedure;

fair process uncrashable \in {1}
begin
  Fair:
    call thread();
end process;

process crashable \in {2}
begin
  Unfair:
    call thread();
end process;
end algorithm;
*)
\* BEGIN TRANSLATION
VARIABLES flags, next_thread, pc, stack

vars == << flags, next_thread, pc, stack >>

ProcSet == ({1}) \cup ({2})

Init == (* Global variables *)
        /\ flags = [t \in Threads |-> FALSE]
        /\ next_thread \in Threads
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {1} -> "Fair"
                                        [] self \in {2} -> "Unfair"]

P1(self) == /\ pc[self] = "P1"
            /\ flags' = [flags EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << next_thread, stack >>

P2(self) == /\ pc[self] = "P2"
            /\ IF \E t \in Threads \ {self}: flags[t]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flags, next_thread, stack >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next_thread /= self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flags, next_thread, stack >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flags' = [flags EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ UNCHANGED << next_thread, stack >>

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next_thread = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flags, next_thread, stack >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flags' = [flags EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ UNCHANGED << next_thread, stack >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flags, next_thread, stack >>

P3(self) == /\ pc[self] = "P3"
            /\ \E thread \in Threads \ {self}:
                 next_thread' = thread
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ UNCHANGED << flags, stack >>

P4(self) == /\ pc[self] = "P4"
            /\ flags' = [flags EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << next_thread, stack >>

P5(self) == /\ pc[self] = "P5"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flags, next_thread, stack >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self) \/ P5(self)

Fair(self) == /\ pc[self] = "Fair"
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                       pc        |->  "Done" ] >>
                                                   \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "P1"]
              /\ UNCHANGED << flags, next_thread >>

uncrashable(self) == Fair(self)

Unfair(self) == /\ pc[self] = "Unfair"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "thread",
                                                         pc        |->  "Done" ] >>
                                                     \o stack[self]]
                /\ pc' = [pc EXCEPT ![self] = "P1"]
                /\ UNCHANGED << flags, next_thread >>

crashable(self) == Unfair(self)

Next == (\E self \in ProcSet: thread(self))
           \/ (\E self \in {1}: uncrashable(self))
           \/ (\E self \in {2}: crashable(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1} : WF_vars(uncrashable(self)) /\ WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AtMostOneCritical ==
  \A t1, t2 \in Threads:
    t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
      
Liveness == \A t \in {1}: <>(pc[t] = "CS")

=============================================================================
\* Modification History
\* Last modified Wed Oct 24 12:44:56 EDT 2018 by john
\* Created Tue Oct 23 15:57:24 EDT 2018 by john
