------------------------------ MODULE knapsack ------------------------------
EXTENDS Integers, TLC
PT == INSTANCE PT

Capacity == 7
Items == {"a", "b", "c"}

HardcodedItemSet == [
  a |-> [size |-> 1, value |-> 1],
  b |-> [size |-> 2, value |-> 3],
  c |-> [size |-> 3, value |-> 1]
]

ItemParams == [size: 2..4, value: 0..5]
ItemSets == [Items -> ItemParams]

KnapsackSum(sack, itemset, prop) ==
    LET value_for(item) == itemset[item][prop] * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)
    
ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSum(sack, itemset, "size") <= Capacity}
    
BestKnapsack(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN CHOOSE best \in all:
        \A worse \in all \ {best}:
        KnapsackSum(worse, itemset, "value") < KnapsackSum(best, itemset, "value")
BestKnapsacksOne(itemset) ==
    LET all == ValidKnapsacks(itemset)
    IN
        CHOOSE best_subset \in SUBSET all:
            \A good \in best_subset: 
                /\ \A also_good \in best_subset:
                    KnapsackSum(good, itemset, "value") = KnapsackSum(also_good, itemset, "value")
                /\ \A bad \in all \ best_subset:
                    KnapsackSum(bad, itemset, "value") < KnapsackSum(good, itemset, "value")

(*--algorithm knapsack

variables itemset \in ItemSets;

begin
    assert BestKnapsacksOne(itemset);
end algorithm*)
\* BEGIN TRANSLATION
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsacksOne(itemset), 
                   "Failure of assertion at line 44, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Sep 26 15:52:24 EDT 2018 by john
\* Created Wed Sep 26 14:22:38 EDT 2018 by john
