---------------------- MODULE definitely_binary_search ----------------------
EXTENDS Integers, Sequences, TLC

PT == INSTANCE PT

MaxInt == 4

OrderedSeq(set, n) == {
  seq \in PT!SeqOf(set, n): 
    \A i \in 2..Len(seq): 
      seq[i] >= seq[i-1]
  }
  
Range(f) == {f[x]: x \in DOMAIN f}

Pow2(n) ==
  LET f[x \in 0..n] ==
    IF x = 0
    THEN 1
    ELSE 2 * f[x-1]
  IN f[n]

(*--algorithm definitely_binary_search
variables 
  seq \in OrderedSeq(1..MaxInt, MaxInt),
  target \in 1..MaxInt,
  found_index = 0,
  low = 1,
  high = Len(seq),
  counter = 0;
  
begin
  Search:
    while low <= high do
      with lh = low + high, mid = lh \div 2 do
        counter := counter + 1;
        if seq[mid] = target then
          found_index := mid;
          goto Result;
        elsif seq[mid] < target then
          if low = high then
            goto Result;
          else
            low := mid + 1;
          end if;
        else
          high := mid - 1;
        end if;
      end with;
    end while;
  Result:
    if Len(seq) > 0 then
      assert Pow2(counter - 1) <= Len(seq);
    end if;
    if target \in Range(seq) then
      assert seq[found_index] = target;
    else
      assert found_index = 0;
    end if;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES seq, target, found_index, low, high, counter, pc

vars == << seq, target, found_index, low, high, counter, pc >>

Init == (* Global variables *)
        /\ seq \in OrderedSeq(1..MaxInt, MaxInt)
        /\ target \in 1..MaxInt
        /\ found_index = 0
        /\ low = 1
        /\ high = Len(seq)
        /\ counter = 0
        /\ pc = "Search"

Search == /\ pc = "Search"
          /\ IF low <= high
                THEN /\ LET lh == low + high IN
                          LET mid == lh \div 2 IN
                            /\ counter' = counter + 1
                            /\ IF seq[mid] = target
                                  THEN /\ found_index' = mid
                                       /\ pc' = "Result"
                                       /\ UNCHANGED << low, high >>
                                  ELSE /\ IF seq[mid] < target
                                             THEN /\ IF low = high
                                                        THEN /\ pc' = "Result"
                                                             /\ low' = low
                                                        ELSE /\ low' = mid + 1
                                                             /\ pc' = "Search"
                                                  /\ high' = high
                                             ELSE /\ high' = mid - 1
                                                  /\ pc' = "Search"
                                                  /\ low' = low
                                       /\ UNCHANGED found_index
                ELSE /\ pc' = "Result"
                     /\ UNCHANGED << found_index, low, high, counter >>
          /\ UNCHANGED << seq, target >>

Result == /\ pc = "Result"
          /\ IF Len(seq) > 0
                THEN /\ Assert(Pow2(counter - 1) <= Len(seq), 
                               "Failure of assertion at line 53, column 7.")
                ELSE /\ TRUE
          /\ IF target \in Range(seq)
                THEN /\ Assert(seq[found_index] = target, 
                               "Failure of assertion at line 56, column 7.")
                ELSE /\ Assert(found_index = 0, 
                               "Failure of assertion at line 58, column 7.")
          /\ pc' = "Done"
          /\ UNCHANGED << seq, target, found_index, low, high, counter >>

Next == Search \/ Result
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

NoOverflows ==
  \A x \in {low, high}:
    x <= MaxInt

=============================================================================
\* Modification History
\* Last modified Thu Oct 25 13:13:16 EDT 2018 by john
\* Created Wed Oct 24 16:40:27 EDT 2018 by john
