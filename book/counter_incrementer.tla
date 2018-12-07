------------------------ MODULE counter_incrementer ------------------------
EXTENDS TLC, Integers

(*--algorithm counter_incrementer
variables counter = 0, goal = 3;

define Success == <>[](counter = goal) end define;

fair process incrementer \in 1..3
variable local = 0;
begin
  GetNSet:
    local := counter;
    counter := local + 1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES counter, goal, pc

(* define statement *)
Success == <>[](counter = goal)

VARIABLE local

vars == << counter, goal, pc, local >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ counter = 0
        /\ goal = 3
        (* Process incrementer *)
        /\ local = [self \in 1..3 |-> 0]
        /\ pc = [self \in ProcSet |-> "GetNSet"]

GetNSet(self) == /\ pc[self] = "GetNSet"
                 /\ local' = [local EXCEPT ![self] = counter]
                 /\ counter' = local'[self] + 1
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ goal' = goal

incrementer(self) == GetNSet(self)

Next == (\E self \in 1..3: incrementer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..3 : WF_vars(incrementer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Thu Oct 25 13:19:16 EDT 2018 by john
\* Created Thu Oct 25 13:13:35 EDT 2018 by john
