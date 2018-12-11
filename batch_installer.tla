-------------------------- MODULE batch_installer --------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Devices, Servers

(*--algorithm batch_installer
variables
  AppScope \in [Devices -> {0, 1}];
  Installs \in [Devices -> BOOLEAN];
  batch_pool = {},
  lock = FALSE;
  
define
  PoolNotEmpty == batch_pool # {}
  
  TypeInvariant == AppScope \in [Devices -> {0, 1}]
  
  Liveness == \A d \in Devices: Installs[d] ~> AppScope[d] = 1
end define;

procedure ChangeAppScope()
variable local = {};
begin
  GetLock:
    await ~lock;
    lock := TRUE;
  Cache:
    local := batch_pool;
  Filter:
    local := {d \in local: AppScope[d] = 0};
  Add:  
    AppScope := [d \in Devices |->
        IF d \in local THEN AppScope[d] + 1
        ELSE AppScope[d] 
     ]; 
  Clean:
    batch_pool := batch_pool \ local;
    lock := FALSE;
  return;
end procedure;

fair process SyncDevice \in Devices
begin 
  Sync:
    if Installs[self] then
        batch_pool := batch_pool \union {self};
    end if;
    goto Sync;
end process;

fair process TimeLoop \in Servers
begin 
  Start:
    while TRUE do
      await PoolNotEmpty;
      either
        call ChangeAppScope();
      or skip;
      end either;
    end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES AppScope, Installs, batch_pool, lock, pc, stack

(* define statement *)
PoolNotEmpty == batch_pool # {}

TypeInvariant == AppScope \in [Devices -> {0, 1}]

Liveness == \A d \in Devices: Installs[d] ~> AppScope[d] = 1

VARIABLE local

vars == << AppScope, Installs, batch_pool, lock, pc, stack, local >>

ProcSet == (Devices) \cup (Servers)

Init == (* Global variables *)
        /\ AppScope \in [Devices -> {0, 1}]
        /\ Installs \in [Devices -> BOOLEAN]
        /\ batch_pool = {}
        /\ lock = FALSE
        (* Procedure ChangeAppScope *)
        /\ local = [ self \in ProcSet |-> {}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Devices -> "Sync"
                                        [] self \in Servers -> "Start"]

GetLock(self) == /\ pc[self] = "GetLock"
                 /\ ~lock
                 /\ lock' = TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Cache"]
                 /\ UNCHANGED << AppScope, Installs, batch_pool, stack, local >>

Cache(self) == /\ pc[self] = "Cache"
               /\ local' = [local EXCEPT ![self] = batch_pool]
               /\ pc' = [pc EXCEPT ![self] = "Filter"]
               /\ UNCHANGED << AppScope, Installs, batch_pool, lock, stack >>

Filter(self) == /\ pc[self] = "Filter"
                /\ local' = [local EXCEPT ![self] = {d \in local[self]: AppScope[d] = 0}]
                /\ pc' = [pc EXCEPT ![self] = "Add"]
                /\ UNCHANGED << AppScope, Installs, batch_pool, lock, stack >>

Add(self) == /\ pc[self] = "Add"
             /\ AppScope' =            [d \in Devices |->
                               IF d \in local[self] THEN AppScope[d] + 1
                               ELSE AppScope[d]
                            ]
             /\ pc' = [pc EXCEPT ![self] = "Clean"]
             /\ UNCHANGED << Installs, batch_pool, lock, stack, local >>

Clean(self) == /\ pc[self] = "Clean"
               /\ batch_pool' = batch_pool \ local[self]
               /\ lock' = FALSE
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ local' = [local EXCEPT ![self] = Head(stack[self]).local]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << AppScope, Installs >>

ChangeAppScope(self) == GetLock(self) \/ Cache(self) \/ Filter(self)
                           \/ Add(self) \/ Clean(self)

Sync(self) == /\ pc[self] = "Sync"
              /\ IF Installs[self]
                    THEN /\ batch_pool' = (batch_pool \union {self})
                    ELSE /\ TRUE
                         /\ UNCHANGED batch_pool
              /\ pc' = [pc EXCEPT ![self] = "Sync"]
              /\ UNCHANGED << AppScope, Installs, lock, stack, local >>

SyncDevice(self) == Sync(self)

Start(self) == /\ pc[self] = "Start"
               /\ PoolNotEmpty
               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ChangeAppScope",
                                                              pc        |->  "Start",
                                                              local     |->  local[self] ] >>
                                                          \o stack[self]]
                     /\ local' = [local EXCEPT ![self] = {}]
                     /\ pc' = [pc EXCEPT ![self] = "GetLock"]
                  \/ /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Start"]
                     /\ UNCHANGED <<stack, local>>
               /\ UNCHANGED << AppScope, Installs, batch_pool, lock >>

TimeLoop(self) == Start(self)

Next == (\E self \in ProcSet: ChangeAppScope(self))
           \/ (\E self \in Devices: SyncDevice(self))
           \/ (\E self \in Servers: TimeLoop(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Devices : WF_vars(SyncDevice(self))
        /\ \A self \in Servers : WF_vars(TimeLoop(self)) /\ WF_vars(ChangeAppScope(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Dec 10 16:06:29 EST 2018 by john
\* Created Mon Dec 10 14:25:00 EST 2018 by john
