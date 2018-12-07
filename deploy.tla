------------------------------- MODULE deploy -------------------------------
EXTENDS TLC, Sequences, FiniteSets, Integers

CONSTANT Servers, MinAvailable, UPDATING

ASSUME Cardinality(Servers) > MinAvailable

(*--algorithm deploy
variables
  server_status = [s \in Servers |-> FALSE],
  load_balancer = Servers;
  
define
  EnoughAvailable == Cardinality(load_balancer) > MinAvailable
  ServersNeedingUpdate == {s \in load_balancer: server_status[s] = FALSE}
  UpdatedServers == {s \in Servers: server_status[s] = TRUE}
  AllDone == \A p \in DOMAIN pc: pc[p] = "Done"
  ServersDidUpdateByEnd == AllDone => \A s \in Servers: server_status[s] = TRUE
  ZeroDowntime == \A s \in load_balancer: server_status[s] /= UPDATING
end define;

process orchestrator = "orchestrator"
begin
  Depool:
  while EnoughAvailable /\ Cardinality(ServersNeedingUpdate) > 0 do
    with victim \in ServersNeedingUpdate do
      load_balancer := load_balancer \ { victim };
    end with;
  end while;
  Repool:
  while Cardinality(UpdatedServers \ load_balancer) > 0 do
    with victim \in UpdatedServers \ load_balancer do
      load_balancer := load_balancer \union {victim};
    end with;
  end while;
  CheckDone:
  if \E s \in Servers: server_status[s] = FALSE then
    goto Depool;
  end if;
end process;
  
fair process server \in Servers
begin
StartUpdate:
  await self \notin load_balancer;
  server_status[self] := UPDATING;
DoUpdate:
  skip;
FinishUpdate:
  server_status[self] := TRUE;
end process;
end algorithm;*)


\* BEGIN TRANSLATION
VARIABLES server_status, load_balancer, pc

(* define statement *)
EnoughAvailable == Cardinality(load_balancer) > MinAvailable
ServersNeedingUpdate == {s \in load_balancer: server_status[s] = FALSE}
UpdatedServers == {s \in Servers: server_status[s] = TRUE}
AllDone == \A p \in DOMAIN pc: pc[p] = "Done"
ServersDidUpdateByEnd == AllDone => \A s \in Servers: server_status[s] = TRUE
ZeroDowntime == \A s \in load_balancer: server_status[s] /= UPDATING


vars == << server_status, load_balancer, pc >>

ProcSet == {"orchestrator"} \cup (Servers)

Init == (* Global variables *)
        /\ server_status = [s \in Servers |-> FALSE]
        /\ load_balancer = Servers
        /\ pc = [self \in ProcSet |-> CASE self = "orchestrator" -> "Depool"
                                        [] self \in Servers -> "StartUpdate"]

Depool == /\ pc["orchestrator"] = "Depool"
          /\ IF EnoughAvailable /\ Cardinality(ServersNeedingUpdate) > 0
                THEN /\ \E victim \in ServersNeedingUpdate:
                          load_balancer' = load_balancer \ { victim }
                     /\ pc' = [pc EXCEPT !["orchestrator"] = "Depool"]
                ELSE /\ pc' = [pc EXCEPT !["orchestrator"] = "Repool"]
                     /\ UNCHANGED load_balancer
          /\ UNCHANGED server_status

Repool == /\ pc["orchestrator"] = "Repool"
          /\ IF Cardinality(UpdatedServers \ load_balancer) > 0
                THEN /\ \E victim \in UpdatedServers \ load_balancer:
                          load_balancer' = (load_balancer \union {victim})
                     /\ pc' = [pc EXCEPT !["orchestrator"] = "Repool"]
                ELSE /\ pc' = [pc EXCEPT !["orchestrator"] = "CheckDone"]
                     /\ UNCHANGED load_balancer
          /\ UNCHANGED server_status

CheckDone == /\ pc["orchestrator"] = "CheckDone"
             /\ IF \E s \in Servers: server_status[s] = FALSE
                   THEN /\ pc' = [pc EXCEPT !["orchestrator"] = "Depool"]
                   ELSE /\ pc' = [pc EXCEPT !["orchestrator"] = "Done"]
             /\ UNCHANGED << server_status, load_balancer >>

orchestrator == Depool \/ Repool \/ CheckDone

StartUpdate(self) == /\ pc[self] = "StartUpdate"
                     /\ self \notin load_balancer
                     /\ server_status' = [server_status EXCEPT ![self] = UPDATING]
                     /\ pc' = [pc EXCEPT ![self] = "DoUpdate"]
                     /\ UNCHANGED load_balancer

DoUpdate(self) == /\ pc[self] = "DoUpdate"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "FinishUpdate"]
                  /\ UNCHANGED << server_status, load_balancer >>

FinishUpdate(self) == /\ pc[self] = "FinishUpdate"
                      /\ server_status' = [server_status EXCEPT ![self] = TRUE]
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED load_balancer

server(self) == StartUpdate(self) \/ DoUpdate(self) \/ FinishUpdate(self)

Next == orchestrator
           \/ (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Servers : WF_vars(server(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Dec 07 11:52:44 EST 2018 by john
\* Created Thu Dec 06 14:57:29 EST 2018 by john
