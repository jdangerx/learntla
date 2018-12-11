--------------------------- MODULE data_pipeline ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS Workers, Scheduler, Jobs

CONSTANTS NULL, IN_PROGRESS, FAILURE, SUCCESS

(*--algorithm data_pipeline
variables
  job_queue = <<>>,
  required_jobs \in SUBSET Jobs,
  job_status = [j \in Jobs |-> NULL],
  all_jobs_processed = FALSE;
  
define
QueuedJobs == {job_queue[i]: i \in DOMAIN job_queue}
SucceededJobs == {j \in Jobs: job_status[j] = SUCCESS}
QueuedJobsFinish ==
  /\ \A j \in Jobs: j \in QueuedJobs ~> job_status[j] = SUCCESS
end define;

process worker \in Workers
variables current = NULL;
begin
Worker:
while ~all_jobs_processed do
  either \* grab a job
    await current = NULL;
    await job_queue /= <<>>;
    GetJob:
      current := Head(job_queue);
      job_queue := Tail(job_queue);
      job_status[current] := IN_PROGRESS;
  or \* fail
    await current /= NULL;
    Fail:
      job_status[current] := FAILURE;
  or \* succeed
    await current /= NULL;
    Succeed:
      job_status[current] := SUCCESS;
  or \* keep working
    skip;
  end either;
end while;
end process;

process scheduler \in {Scheduler}
begin
Schedule:
  while TRUE do
    await required_jobs \ SucceededJobs /= {};
    QueueJob:
    with job \in required_jobs \ SucceededJobs do
      job_queue := Append(job_queue, job)
    end with;
  end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES job_queue, required_jobs, job_status, all_jobs_processed, pc

(* define statement *)
QueuedJobs == {job_queue[i]: i \in DOMAIN job_queue}
SucceededJobs == {j \in Jobs: job_status[j] = SUCCESS}
QueuedJobsFinish ==
  /\ \A j \in Jobs: j \in QueuedJobs ~> job_status[j] = SUCCESS

VARIABLE current

vars == << job_queue, required_jobs, job_status, all_jobs_processed, pc, 
           current >>

ProcSet == (Workers) \cup ({Scheduler})

Init == (* Global variables *)
        /\ job_queue = <<>>
        /\ required_jobs \in SUBSET Jobs
        /\ job_status = [j \in Jobs |-> NULL]
        /\ all_jobs_processed = FALSE
        (* Process worker *)
        /\ current = [self \in Workers |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in Workers -> "Worker"
                                        [] self \in {Scheduler} -> "Schedule"]

Worker(self) == /\ pc[self] = "Worker"
                /\ IF ~all_jobs_processed
                      THEN /\ \/ /\ current[self] = NULL
                                 /\ job_queue /= <<>>
                                 /\ pc' = [pc EXCEPT ![self] = "GetJob"]
                              \/ /\ current[self] /= NULL
                                 /\ pc' = [pc EXCEPT ![self] = "Fail"]
                              \/ /\ current[self] /= NULL
                                 /\ pc' = [pc EXCEPT ![self] = "Succeed"]
                              \/ /\ TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "Worker"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << job_queue, required_jobs, job_status, 
                                all_jobs_processed, current >>

GetJob(self) == /\ pc[self] = "GetJob"
                /\ current' = [current EXCEPT ![self] = Head(job_queue)]
                /\ job_queue' = Tail(job_queue)
                /\ job_status' = [job_status EXCEPT ![current'[self]] = IN_PROGRESS]
                /\ pc' = [pc EXCEPT ![self] = "Worker"]
                /\ UNCHANGED << required_jobs, all_jobs_processed >>

Fail(self) == /\ pc[self] = "Fail"
              /\ job_status' = [job_status EXCEPT ![current[self]] = FAILURE]
              /\ pc' = [pc EXCEPT ![self] = "Worker"]
              /\ UNCHANGED << job_queue, required_jobs, all_jobs_processed, 
                              current >>

Succeed(self) == /\ pc[self] = "Succeed"
                 /\ job_status' = [job_status EXCEPT ![current[self]] = SUCCESS]
                 /\ pc' = [pc EXCEPT ![self] = "Worker"]
                 /\ UNCHANGED << job_queue, required_jobs, all_jobs_processed, 
                                 current >>

worker(self) == Worker(self) \/ GetJob(self) \/ Fail(self) \/ Succeed(self)

Schedule(self) == /\ pc[self] = "Schedule"
                  /\ required_jobs \ SucceededJobs /= {}
                  /\ pc' = [pc EXCEPT ![self] = "QueueJob"]
                  /\ UNCHANGED << job_queue, required_jobs, job_status, 
                                  all_jobs_processed, current >>

QueueJob(self) == /\ pc[self] = "QueueJob"
                  /\ \E job \in required_jobs \ SucceededJobs:
                       job_queue' = Append(job_queue, job)
                  /\ pc' = [pc EXCEPT ![self] = "Schedule"]
                  /\ UNCHANGED << required_jobs, job_status, 
                                  all_jobs_processed, current >>

scheduler(self) == Schedule(self) \/ QueueJob(self)

Next == (\E self \in Workers: worker(self))
           \/ (\E self \in {Scheduler}: scheduler(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Dec 11 12:19:42 EST 2018 by john
\* Created Mon Dec 10 17:00:09 EST 2018 by john
