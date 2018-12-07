-------------------------------- MODULE max --------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANT IntSet, MaxSeqLen

ASSUME IntSet \subseteq Int
ASSUME MaxSeqLen > 0


PT == INSTANCE PT

Max(seq) ==
  LET set == {seq[i]: i \in 1..Len(seq)}
  IN CHOOSE x \in set: \A y \in set: y <= x
  
AllInputs == PT!SeqOf(IntSet, MaxSeqLen)

  
(*--algorithm max
variables
  seq \in AllInputs \ {<<>>},
  i = 1, 
  max = seq[1];
  
begin
  assert Len(seq) > 0;
  while i <= Len(seq) do
    if seq[i] > max then
      max := seq[i];
    end if;
    i := i + 1;
  end while;
  assert max = Max(seq);
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES seq, i, max, pc

vars == << seq, i, max, pc >>

Init == (* Global variables *)
        /\ seq \in AllInputs \ {<<>>}
        /\ i = 1
        /\ max = seq[1]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Len(seq) > 0, 
                   "Failure of assertion at line 26, column 3.")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << seq, i, max >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= Len(seq)
               THEN /\ IF seq[i] > max
                          THEN /\ max' = seq[i]
                          ELSE /\ TRUE
                               /\ max' = max
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(max = Max(seq), 
                              "Failure of assertion at line 33, column 3.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << i, max >>
         /\ seq' = seq

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Wed Oct 24 15:42:51 EDT 2018 by john
\* Created Wed Oct 24 14:56:30 EDT 2018 by john
