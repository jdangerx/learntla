------------------------------ MODULE leftpad ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Characters

PT == INSTANCE PT

Leftpad(c, n, s) ==
  IF n < 0 THEN s ELSE
  LET
    padded_length == PT!Max(n, Len(s))
    to_pad == CHOOSE x \in 0..n: x + Len(s) = padded_length
  IN
    [x \in 1..to_pad |-> c] \o s
     

(*--algorithm leftpad
variables
  in_c \in Characters \union {" "},
  in_n \in 0..6,
  in_s \in PT!SeqOf(Characters, 6),
  out_s = in_s;
begin
  while Len(out_s) < in_n do
    out_s := <<in_c>> \o out_s
  end while;
  assert out_s = Leftpad(in_c, in_n, in_s)
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES in_c, in_n, in_s, out_s, pc

vars == << in_c, in_n, in_s, out_s, pc >>

Init == (* Global variables *)
        /\ in_c \in (Characters \union {" "})
        /\ in_n \in 0..6
        /\ in_s \in PT!SeqOf(Characters, 6)
        /\ out_s = in_s
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(out_s) < in_n
               THEN /\ out_s' = <<in_c>> \o out_s
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(out_s = Leftpad(in_c, in_n, in_s), 
                              "Failure of assertion at line 27, column 3.")
                    /\ pc' = "Done"
                    /\ out_s' = out_s
         /\ UNCHANGED << in_c, in_n, in_s >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Oct 24 16:27:22 EDT 2018 by john
\* Created Wed Oct 24 15:57:06 EDT 2018 by john
