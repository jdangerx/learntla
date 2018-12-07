-------------------------------- MODULE add --------------------------------
EXTENDS TLC, Integers

Expected(x, y) == x + y

(*--algorithm add

variables a \in -5..5, b \in -5..5, output;

begin
output := a + b;
assert Expected(a, b) = output 

end algorithm;*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES a, b, output, pc

vars == << a, b, output, pc >>

Init == (* Global variables *)
        /\ a \in -5..5
        /\ b \in -5..5
        /\ output = defaultInitValue
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ output' = a + b
         /\ Assert(Expected(a, b) = output', 
                   "Failure of assertion at line 12, column 1.")
         /\ pc' = "Done"
         /\ UNCHANGED << a, b >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Correct == <>(output = Expected(a, b))  



=============================================================================
\* Modification History
\* Last modified Wed Oct 24 14:55:24 EDT 2018 by john
\* Created Wed Oct 24 14:50:54 EDT 2018 by john
