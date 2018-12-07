---------------------------- MODULE LinkedLists ----------------------------
CONSTANT NULL

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC


PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

Range(f) == {f[i]: i \in DOMAIN f}

isLinkedList(PointerMap) ==
  LET
    nodes == DOMAIN PointerMap
    all_seqs == [1..Cardinality(nodes) -> nodes]
  IN 
    \E ordering \in all_seqs:
      /\ \A i \in 1..Len(ordering)-1:
        PointerMap[ordering[i]] = ordering[i+1]
      /\ nodes \subseteq Range(ordering)   

LinkedLists(Nodes) ==
  IF NULL \in Nodes
  THEN Assert(FALSE, "NULL cannot be in Nodes")
  ELSE 
    LET
      subsets == SUBSET Nodes \ {{}}
      submaps == {PointerMaps(sub): sub \in subsets}
    IN
      {pm \in UNION submaps: isLinkedList(pm)}
      
Ring(ll) == DOMAIN ll = Range(ll)

First(ll) ==
  CHOOSE node \in DOMAIN ll:
    ~Ring(ll) => node \notin Range(ll)

Cyclic(ll) == NULL \notin Range(ll)

=============================================================================
\* Modification History
\* Last modified Thu Oct 25 14:15:33 EDT 2018 by john
\* Created Thu Oct 25 13:52:31 EDT 2018 by john
