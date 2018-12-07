------------------------------ MODULE traffic ------------------------------
EXTENDS TLC, Integers

NextColor(c) == 
    CASE c = "green" -> "red"
      [] c = "red" -> "green"


(*--algorithm traffic

variables at_light = TRUE, color = "red";

process light = "light"
begin
Toggle:
    while TRUE do
        color := NextColor(color); 
    end while;
end process;

process car = "car"
begin
Drive:
    when color = "green";
    at_light := FALSE; 
end process;


end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES at_light, color, pc

vars == << at_light, color, pc >>

ProcSet == {"light"} \cup {"car"}

Init == (* Global variables *)
        /\ at_light = TRUE
        /\ color = "red"
        /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Toggle"
                                        [] self = "car" -> "Drive"]

Toggle == /\ pc["light"] = "Toggle"
          /\ color' = NextColor(color)
          /\ pc' = [pc EXCEPT !["light"] = "Toggle"]
          /\ UNCHANGED at_light

light == Toggle

Drive == /\ pc["car"] = "Drive"
         /\ color = "green"
         /\ at_light' = FALSE
         /\ pc' = [pc EXCEPT !["car"] = "Done"]
         /\ color' = color

car == Drive

Next == light \/ car

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Oct 23 14:32:23 EDT 2018 by john
\* Created Mon Oct 01 15:02:27 EDT 2018 by john
