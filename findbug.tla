------------------------------ MODULE findbug ------------------------------
EXTENDS TLC, Integers, Sequences
CONSTANT Threads, BufLen
(*--algorithm findbug
variables
  put_at = 0,
  take_at = 0,
  occupied = 0,
  buffer = <<>>,
  awake = [t \in Threads |-> TRUE];
  
define
  SleepingThreads == {t \in Threads: ~awake[t]}
  OccupyBoundsCheck == occupied >= 0 /\ occupied < BufLen - 1
end define;

macro notify() begin
  with t \in SleepingThreads do
    awake[t] := TRUE;
  end with;
end macro;

process thread \in Threads
begin
Thread:
  await awake[t];
  either \*put
    if occupied = BufLen then
      awake[t] := FALSE;
      goto Thread;
    end if;
    notify();
    occupied := occupied + 1;
  or \* take
    if occupied = 0 then
      awake[t] := FALSE;
      goto Thread;
    end if;
    notify();
    occupied := occupied - 1;
  end either;
end process;

end algorithm;*)

=============================================================================
\* Modification History
\* Last modified Fri Dec 07 12:10:00 EST 2018 by john
\* Created Fri Dec 07 11:58:46 EST 2018 by john
