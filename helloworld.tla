----------------------------- MODULE helloworld -----------------------------
EXTENDS TLC

(* --algorithm helloworld
variable s \in {"Hello", "world"};

begin
    A:
        print s;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES s, pc

vars == << s, pc >>

Init == (* Global variables *)
        /\ s \in {"Hello", "world"}
        /\ pc = "A"

A == /\ pc = "A"
     /\ PrintT(s)
     /\ pc' = "Done"
     /\ s' = s

Next == A
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Sep 24 16:50:38 EDT 2018 by john
\* Created Mon Sep 24 16:49:02 EDT 2018 by john
