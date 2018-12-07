------------------------------- MODULE cache -------------------------------
EXTENDS TLC, Integers
CONSTANT ResourceCap, MaxReq, Consumers

ASSUME ResourceCap > 0
ASSUME Consumers /= {}
ASSUME MaxReq \in 1..ResourceCap

(*--algorithm cache
variable
    cap \in 1..ResourceCap,
    remaining = cap,
    reserved = 0;

define
    ResourcesExist == remaining >= 0
end define;

process consumer \in Consumers
variables req \in 1..MaxReq
begin
    WaitForResources:
        while TRUE do
            await reserved + req <= remaining;
            reserved := reserved + req;
            Nibble:
            while req > 0 do
                remaining := remaining - 1;
                req := req - 1;
                reserved := reserved - 1;
            end while;
            GetNewReq:
            with x \in 1..MaxReq do
                req := x;
            end with;
        end while;
end process;

process time = "time"
begin
    Tick:
        remaining := cap;
        goto Tick;
end process;
end algorithm*)
\* BEGIN TRANSLATION
VARIABLES cap, remaining, reserved, pc

(* define statement *)
ResourcesExist == remaining >= 0

VARIABLE req

vars == << cap, remaining, reserved, pc, req >>

ProcSet == (Consumers) \cup {"time"}

Init == (* Global variables *)
        /\ cap \in 1..ResourceCap
        /\ remaining = cap
        /\ reserved = 0
        (* Process consumer *)
        /\ req \in [Consumers -> 1..MaxReq]
        /\ pc = [self \in ProcSet |-> CASE self \in Consumers -> "WaitForResources"
                                        [] self = "time" -> "Tick"]

WaitForResources(self) == /\ pc[self] = "WaitForResources"
                          /\ reserved + req[self] <= remaining
                          /\ reserved' = reserved + req[self]
                          /\ pc' = [pc EXCEPT ![self] = "Nibble"]
                          /\ UNCHANGED << cap, remaining, req >>

Nibble(self) == /\ pc[self] = "Nibble"
                /\ IF req[self] > 0
                      THEN /\ remaining' = remaining - 1
                           /\ req' = [req EXCEPT ![self] = req[self] - 1]
                           /\ reserved' = reserved - 1
                           /\ pc' = [pc EXCEPT ![self] = "Nibble"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "GetNewReq"]
                           /\ UNCHANGED << remaining, reserved, req >>
                /\ cap' = cap

GetNewReq(self) == /\ pc[self] = "GetNewReq"
                   /\ \E x \in 1..MaxReq:
                        req' = [req EXCEPT ![self] = x]
                   /\ pc' = [pc EXCEPT ![self] = "WaitForResources"]
                   /\ UNCHANGED << cap, remaining, reserved >>

consumer(self) == WaitForResources(self) \/ Nibble(self) \/ GetNewReq(self)

Tick == /\ pc["time"] = "Tick"
        /\ remaining' = cap
        /\ pc' = [pc EXCEPT !["time"] = "Tick"]
        /\ UNCHANGED << cap, reserved, req >>

time == Tick

Next == time
           \/ (\E self \in Consumers: consumer(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Oct 01 14:42:05 EDT 2018 by john
\* Created Mon Oct 01 14:06:11 EDT 2018 by john
