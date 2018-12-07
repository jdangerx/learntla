-------------------------------- MODULE main --------------------------------
EXTENDS Integers, TLC, FiniteSets, Sequences

CONSTANT MYNULL

LL == INSTANCE LinkedLists WITH NULL <- MYNULL

Nodes == 1..3

HasCycle(lls) == \E ll \in lls: LL!Cyclic(ll)
HasWithoutCycle(lls) == \E ll \in lls: ~LL!Cyclic(ll)
HasCoveringRing(nodes) ==
  \E ll \in LL!LinkedLists(nodes):
    /\ LL!Ring(ll)
    /\ DOMAIN ll = nodes
    
NumOrphans(ll) == Cardinality(DOMAIN ll \ LL!Range(ll))

NumParents(node, ll) == Cardinality({parent \in DOMAIN ll: ll[parent] = node})


OnlyCyclesHaveTwoParents(lls) ==
  \A ll \in lls:
    LET
      numWithTwoParents == Cardinality({n \in DOMAIN ll: NumParents(n, ll) = 2})
    IN
      /\ numWithTwoParents <= 1
      /\ numWithTwoParents > 0 => LL!Cyclic(ll)

MaxParentNum(ll) ==
  LET numParents == {NumParents(n, ll): n \in DOMAIN ll}
  IN 
    CHOOSE x \in numParents: \A y \in numParents: x >= y
    
NoPolyFamilies(lls) == \A ll \in lls: MaxParentNum(ll) <= 2

Valid == 
  LET lls == LL!LinkedLists(Nodes)
  IN
    /\ HasCycle(lls)
    /\ HasWithoutCycle(lls)
    /\ HasCoveringRing(Nodes)
    /\ \A ll \in lls: (LL!Cyclic(ll) /\ NumOrphans(ll) = 0) \/ NumOrphans(ll) = 1
    /\ OnlyCyclesHaveTwoParents(lls)
    /\ NoPolyFamilies(lls)

(*--algorithm main
variables
  ll \in LL!LinkedLists(Nodes),
  tortoise = LL!First(ll),
  hare = LL!First(ll);

macro advance(pointer) begin
  pointer := ll[pointer];
  if pointer = MYNULL then
    assert ~LL!Cyclic(ll);
    goto Done;
  end if;
end macro;

begin
  L1:
  while tortoise /= MYNULL /\ hare /= MYNULL do
    L2: advance(tortoise);
    L3: advance(hare);
    L4: advance(hare);
    L5: if tortoise = hare then
      assert LL!Cyclic(ll);
      goto Done;
    end if;
  end while;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES ll, tortoise, hare, pc

vars == << ll, tortoise, hare, pc >>

Init == (* Global variables *)
        /\ ll \in LL!LinkedLists(Nodes)
        /\ tortoise = LL!First(ll)
        /\ hare = LL!First(ll)
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ IF tortoise /= MYNULL /\ hare /= MYNULL
            THEN /\ pc' = "L2"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << ll, tortoise, hare >>

L2 == /\ pc = "L2"
      /\ tortoise' = ll[tortoise]
      /\ IF tortoise' = MYNULL
            THEN /\ Assert(~LL!Cyclic(ll), 
                           "Failure of assertion at line 56, column 5 of macro called at line 64, column 9.")
                 /\ pc' = "Done"
            ELSE /\ pc' = "L3"
      /\ UNCHANGED << ll, hare >>

L3 == /\ pc = "L3"
      /\ hare' = ll[hare]
      /\ IF hare' = MYNULL
            THEN /\ Assert(~LL!Cyclic(ll), 
                           "Failure of assertion at line 56, column 5 of macro called at line 65, column 9.")
                 /\ pc' = "Done"
            ELSE /\ pc' = "L4"
      /\ UNCHANGED << ll, tortoise >>

L4 == /\ pc = "L4"
      /\ hare' = ll[hare]
      /\ IF hare' = MYNULL
            THEN /\ Assert(~LL!Cyclic(ll), 
                           "Failure of assertion at line 56, column 5 of macro called at line 66, column 9.")
                 /\ pc' = "Done"
            ELSE /\ pc' = "L5"
      /\ UNCHANGED << ll, tortoise >>

L5 == /\ pc = "L5"
      /\ IF tortoise = hare
            THEN /\ Assert(LL!Cyclic(ll), 
                           "Failure of assertion at line 68, column 7.")
                 /\ pc' = "Done"
            ELSE /\ pc' = "L1"
      /\ UNCHANGED << ll, tortoise, hare >>

Next == L1 \/ L2 \/ L3 \/ L4 \/ L5
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Oct 25 17:23:08 EDT 2018 by john
\* Created Thu Oct 25 13:52:02 EDT 2018 by john
