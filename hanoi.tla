------------------------------- MODULE hanoi -------------------------------

EXTENDS TLC, Sequences, Integers

(* --algorithm hanoi

variables towers = << << 1, 2, 3 >>, <<>>, <<>> >>;

define D == DOMAIN(towers) end define

begin
  while TRUE do
    assert towers[3] /= << 1, 2, 3 >>;
    with src \in { x \in D : towers[x] /= <<>> },
         dst \in {
           y \in D:
             \/ towers[y] = <<>> 
             \/ Head(towers[src]) < Head(towers[y])
         } do
      towers[src] := Tail(towers[src]) ||
      towers[dst] := << Head(towers[src]) >> \o towers[dst];
    end with;
  end while;
  

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLE towers

(* define statement *)
D == DOMAIN(towers)


vars == << towers >>

Init == (* Global variables *)
        /\ towers = << << 1, 2, 3 >>, <<>>, <<>> >>

Next == /\ Assert(towers[3] /= << 1, 2, 3 >>, 
                  "Failure of assertion at line 13, column 5.")
        /\ \E src \in { x \in D : towers[x] /= <<>> }:
             \E dst \in         {
                          y \in D:
                            \/ towers[y] = <<>>
                            \/ Head(towers[src]) < Head(towers[y])
                        }:
               towers' = [towers EXCEPT ![src] = Tail(towers[src]),
                                        ![dst] = << Head(towers[src]) >> \o towers[dst]]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Sep 25 15:39:52 EDT 2018 by john
\* Created Tue Sep 25 14:18:42 EDT 2018 by john
