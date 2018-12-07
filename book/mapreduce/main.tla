-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

PT == INSTANCE PT

CONSTANTS Workers, Reducer, ItemRange, ItemCount, NULL

ASSUME ItemRange \subseteq Nat
ASSUME ItemCount \in Nat

FairWorkers == CHOOSE singleton \in SUBSET Workers: Cardinality(singleton) = 1
UnfairWorkers == Workers \ FairWorkers
PossibleInputs == PT!TupleOf(ItemRange, ItemCount)

SumSeq(seq) == PT!ReduceSeq(+, seq, 0)

(*--algorithm mapreduce
variables
  input \in PossibleInputs,
  results = [w \in Workers |-> [total |-> NULL, count |-> NULL]],
  queue = [w \in Workers |-> <<>>],
  status = [w \in Workers |-> "inactive"]; \* only for reducer!
  
define
  ActiveWorkers == {w \in Workers: status[w] = "active"}
  HealthyWorkers == {w \in Workers: status[w] /= "broken"}

  TypeInvariant ==
    /\ status \in [Workers -> {"inactive", "active", "broken"}]
    /\ \A w \in Workers:
      /\ Len(queue[w]) <= ItemCount
      /\ \A i \in 1..Len(queue[w]):
        queue[w][i] \in ItemRange
      /\ \/ results[w].total = NULL
         \/ results[w].total <= SumSeq(input)
      /\ \/ results[w].count = NULL
         \/ results[w].count <= Len(input)
end define;

macro reduce() begin
  with w \in {w \in ActiveWorkers:
        /\ results[w].count = Len(assigned[w])
      } do
    final[w] := results[w].total;
    status[w] := "inactive";
  end with;
end macro;

procedure work()
variables total = 0, count = 0;
begin
  WaitForInit:
    await queue[self] /= <<>>;
  Work:
    while queue[self] /= <<>> do
      total := total + Head(queue[self]);
      count := count + 1;
      queue[self] := Tail(queue[self]);
    end while;
  Result:
    results[self] := [total |-> total, count |-> count];
  goto WaitForInit;
end procedure;

fair process reducer \in {Reducer}
variables
  final = [w \in Workers |-> 0], 
  assigned = [w \in Workers |-> <<>>];
begin
  Schedule:
    with worker_order = PT!OrderSet(Workers) do
      queue := [
        w \in Workers |->
          LET Offset == PT!Index(worker_order, w) - 1
          IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = Offset) 
      ];
      assigned := queue;
      status := [
        w \in Workers |->
          IF Len(assigned[w]) = 0 
          THEN "inactive" 
          -ELSE "active
      ]      
    end with;
  ReduceResults:
    while ActiveWorkers /= {} do
      either
        \* Reduce
        reduce();
      or
        \* Reassign
        with 
          from_worker \in ActiveWorkers \ FairWorkers, 
          to_worker \in HealthyWorkers \ {from_worker} do

          status[from_worker] := "broken" ||
          status[to_worker] := "active";
          
          queue[to_worker] := queue[to_worker] \o assigned[from_worker]; 
          
          assigned[to_worker] := assigned[to_worker] \o assigned[from_worker];
          
          final[to_worker] := 0;
        end with;
      end either;
    end while;
  Finish:
    assert SumSeq(final) = SumSeq(input)
end process;

fair process fair_worker \in FairWorkers
begin
  FairWorker:
    call work();
end process; 

process worker \in UnfairWorkers
begin
  Worker:
    call work();
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES input, results, queue, status, pc, stack

(* define statement *)
ActiveWorkers == {w \in Workers: status[w] = "active"}
HealthyWorkers == {w \in Workers: status[w] /= "broken"}

TypeInvariant ==
  /\ status \in [Workers -> {"inactive", "active", "broken"}]
  /\ \A w \in Workers:
    /\ Len(queue[w]) <= ItemCount
    /\ \A i \in 1..Len(queue[w]):
      queue[w][i] \in ItemRange
    /\ \/ results[w].total = NULL
       \/ results[w].total <= SumSeq(input)
    /\ \/ results[w].count = NULL
       \/ results[w].count <= Len(input)

VARIABLES total, count, final, assigned

vars == << input, results, queue, status, pc, stack, total, count, final, 
           assigned >>

ProcSet == ({Reducer}) \cup (FairWorkers) \cup (UnfairWorkers)

Init == (* Global variables *)
        /\ input \in PossibleInputs
        /\ results = [w \in Workers |-> [total |-> NULL, count |-> NULL]]
        /\ queue = [w \in Workers |-> <<>>]
        /\ status = [w \in Workers |-> "inactive"]
        (* Procedure work *)
        /\ total = [ self \in ProcSet |-> 0]
        /\ count = [ self \in ProcSet |-> 0]
        (* Process reducer *)
        /\ final = [self \in {Reducer} |-> [w \in Workers |-> 0]]
        /\ assigned = [self \in {Reducer} |-> [w \in Workers |-> <<>>]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {Reducer} -> "Schedule"
                                        [] self \in FairWorkers -> "FairWorker"
                                        [] self \in UnfairWorkers -> "Worker"]

WaitForInit(self) == /\ pc[self] = "WaitForInit"
                     /\ queue[self] /= <<>>
                     /\ pc' = [pc EXCEPT ![self] = "Work"]
                     /\ UNCHANGED << input, results, queue, status, stack, 
                                     total, count, final, assigned >>

Work(self) == /\ pc[self] = "Work"
              /\ IF queue[self] /= <<>>
                    THEN /\ total' = [total EXCEPT ![self] = total[self] + Head(queue[self])]
                         /\ count' = [count EXCEPT ![self] = count[self] + 1]
                         /\ queue' = [queue EXCEPT ![self] = Tail(queue[self])]
                         /\ pc' = [pc EXCEPT ![self] = "Work"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Result"]
                         /\ UNCHANGED << queue, total, count >>
              /\ UNCHANGED << input, results, status, stack, final, assigned >>

Result(self) == /\ pc[self] = "Result"
                /\ results' = [results EXCEPT ![self] = [total |-> total[self], count |-> count[self]]]
                /\ pc' = [pc EXCEPT ![self] = "WaitForInit"]
                /\ UNCHANGED << input, queue, status, stack, total, count, 
                                final, assigned >>

work(self) == WaitForInit(self) \/ Work(self) \/ Result(self)

Schedule(self) == /\ pc[self] = "Schedule"
                  /\ LET worker_order == PT!OrderSet(Workers) IN
                       /\ queue' =          [
                                     w \in Workers |->
                                       LET Offset == PT!Index(worker_order, w) - 1
                                       IN PT!SelectSeqByIndex(input, LAMBDA i: i % Len(worker_order) = Offset)
                                   ]
                       /\ assigned' = [assigned EXCEPT ![self] = queue']
                       /\ status' =           [
                                      w \in Workers |->
                                        CASE Len(assigned'[self][w]) = 0 -> "inactive"
                                          [] OTHER -> "active"
                                    ]
                  /\ pc' = [pc EXCEPT ![self] = "ReduceResults"]
                  /\ UNCHANGED << input, results, stack, total, count, final >>

ReduceResults(self) == /\ pc[self] = "ReduceResults"
                       /\ IF ActiveWorkers /= {}
                             THEN /\ \/ /\ \E w \in        {w \in ActiveWorkers:
                                                      /\ results[w].count = Len(assigned[self][w])
                                                    }:
                                             /\ final' = [final EXCEPT ![self][w] = results[w].total]
                                             /\ status' = [status EXCEPT ![w] = "inactive"]
                                        /\ UNCHANGED <<queue, assigned>>
                                     \/ /\ \E from_worker \in ActiveWorkers \ FairWorkers:
                                             \E to_worker \in HealthyWorkers \ {from_worker}:
                                               /\ status' = [status EXCEPT ![from_worker] = "broken",
                                                                           ![to_worker] = "active"]
                                               /\ queue' = [queue EXCEPT ![to_worker] = queue[to_worker] \o assigned[self][from_worker]]
                                               /\ assigned' = [assigned EXCEPT ![self][to_worker] = assigned[self][to_worker] \o assigned[self][from_worker]]
                                               /\ final' = [final EXCEPT ![self][to_worker] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "ReduceResults"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Finish"]
                                  /\ UNCHANGED << queue, status, final, 
                                                  assigned >>
                       /\ UNCHANGED << input, results, stack, total, count >>

Finish(self) == /\ pc[self] = "Finish"
                /\ Assert(SumSeq(final[self]) = SumSeq(input), 
                          "Failure of assertion at line 107, column 5.")
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << input, results, queue, status, stack, total, 
                                count, final, assigned >>

reducer(self) == Schedule(self) \/ ReduceResults(self) \/ Finish(self)

FairWorker(self) == /\ pc[self] = "FairWorker"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                             pc        |->  "Done",
                                                             total     |->  total[self],
                                                             count     |->  count[self] ] >>
                                                         \o stack[self]]
                    /\ total' = [total EXCEPT ![self] = 0]
                    /\ count' = [count EXCEPT ![self] = 0]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForInit"]
                    /\ UNCHANGED << input, results, queue, status, final, 
                                    assigned >>

fair_worker(self) == FairWorker(self)

Worker(self) == /\ pc[self] = "Worker"
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "work",
                                                         pc        |->  "Done",
                                                         total     |->  total[self],
                                                         count     |->  count[self] ] >>
                                                     \o stack[self]]
                /\ total' = [total EXCEPT ![self] = 0]
                /\ count' = [count EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "WaitForInit"]
                /\ UNCHANGED << input, results, queue, status, final, assigned >>

worker(self) == Worker(self)

Next == (\E self \in ProcSet: work(self))
           \/ (\E self \in {Reducer}: reducer(self))
           \/ (\E self \in FairWorkers: fair_worker(self))
           \/ (\E self \in UnfairWorkers: worker(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {Reducer} : WF_vars(reducer(self))
        /\ \A self \in FairWorkers : WF_vars(fair_worker(self)) /\ WF_vars(work(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


Liveness ==
  <>[](
    SumSeq(final[Reducer]) = SumSeq(input)
  )
  
ReducerFinishes ==
  <>(pc[Reducer] = "Finish")

=============================================================================
\* Modification History
\* Last modified Thu Nov 01 22:46:21 EDT 2018 by john
\* Created Wed Oct 31 12:37:38 EDT 2018 by john
