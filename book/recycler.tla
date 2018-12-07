------------------------------ MODULE recycler ------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

BinTypes == {"trash", "recycling"}
Items == [type: BinTypes, size: 1..6]
SetsOfFour(s) == s \X s \X s \X s
SeqOf(set, count) ==
  [1..count -> set]

(*--algorithm recycler
variables
    capacity \in [trash: 1..10, recycling: 1..10],
    bins = [trash |-> {}, recycling |-> {}],
    count = [trash |-> 0, recycling |-> 0],
    items \in SeqOf(Items, 1..5),
    curr = "";
    
define 
    NoBinOverflow == \A type \in BinTypes: capacity[type] >= 0
    CountsMatchUp == \A type \in BinTypes: Cardinality(bins[type]) = count[type]
            
end define;
    
macro add_to_bin(type, item) begin
    capacity[type] := capacity[type] - item.size;
    bins[type] := bins[type] \union {item};
    count[type] := count[type] + 1;
end macro;

begin
    while items /= << >> do
        curr := Head(items);
        items := Tail(items); 
        if capacity[curr.type] > curr.size then
            add_to_bin(curr.type, curr)
        elsif curr.type = "recycling" /\ capacity.trash > curr.size then
            add_to_bin("trash", curr)
        end if;
    end while;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES capacity, bins, count, items, curr, pc

(* define statement *)
NoBinOverflow == \A type \in BinTypes: capacity[type] >= 0
CountsMatchUp == \A type \in BinTypes: Cardinality(bins[type]) = count[type]


vars == << capacity, bins, count, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycling: 1..10]
        /\ bins = [trash |-> {}, recycling |-> {}]
        /\ count = [trash |-> 0, recycling |-> 0]
        /\ items \in SetsOfFour(Items)
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= << >>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF capacity[curr'.type] > curr'.size
                          THEN /\ capacity' = [capacity EXCEPT ![(curr'.type)] = capacity[(curr'.type)] - curr'.size]
                               /\ bins' = [bins EXCEPT ![(curr'.type)] = bins[(curr'.type)] \union {curr'}]
                               /\ count' = [count EXCEPT ![(curr'.type)] = count[(curr'.type)] + 1]
                          ELSE /\ IF curr'.type = "recycling" /\ capacity.trash > curr'.size
                                     THEN /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ bins' = [bins EXCEPT !["trash"] = bins["trash"] \union {curr'}]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Sep 26 14:20:21 EDT 2018 by john
\* Created Tue Sep 25 16:53:00 EDT 2018 by john
