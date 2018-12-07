-------------------------------- MODULE door --------------------------------
EXTENDS TLC

(*--algorithm door
variables
  open = FALSE,
  locked = FALSE,
  key \in BOOLEAN;


process unlocked_door = "Unlocked Door"
begin
  UnlockedDoor:
  await ~locked;
  either \* lock
    await open \/ key;
    locked := TRUE;
  or \* open
    await ~open;
    open := TRUE;
  or \* close
    await open;
    open := FALSE;
  end either;
  goto UnlockedDoor;
end process;

process locked_door = "Locked Door"
begin
  LockedDoor:
  await locked;
\*  either \* unlock
    await open \/ key;
    locked := FALSE;
\*  or \* close
\*    await open;
\*    open := FALSE;
\*  end either;
  goto LockedDoor;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES open, locked, key, pc

vars == << open, locked, key, pc >>

ProcSet == {"Unlocked Door"} \cup {"Locked Door"}

Init == (* Global variables *)
        /\ open = FALSE
        /\ locked = FALSE
        /\ key \in BOOLEAN
        /\ pc = [self \in ProcSet |-> CASE self = "Unlocked Door" -> "UnlockedDoor"
                                        [] self = "Locked Door" -> "LockedDoor"]

UnlockedDoor == /\ pc["Unlocked Door"] = "UnlockedDoor"
                /\ ~locked
                /\ \/ /\ open \/ key
                      /\ locked' = TRUE
                      /\ open' = open
                   \/ /\ ~open
                      /\ open' = TRUE
                      /\ UNCHANGED locked
                   \/ /\ open
                      /\ open' = FALSE
                      /\ UNCHANGED locked
                /\ pc' = [pc EXCEPT !["Unlocked Door"] = "UnlockedDoor"]
                /\ key' = key

unlocked_door == UnlockedDoor

LockedDoor == /\ pc["Locked Door"] = "LockedDoor"
              /\ locked
              /\ open \/ key
              /\ locked' = FALSE
              /\ pc' = [pc EXCEPT !["Locked Door"] = "LockedDoor"]
              /\ UNCHANGED << open, key >>

locked_door == LockedDoor

Next == unlocked_door \/ locked_door
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Oct 26 15:05:36 EDT 2018 by john
\* Created Fri Oct 26 14:38:52 EDT 2018 by john
