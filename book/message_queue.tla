--------------------------- MODULE message_queue ---------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MaxQueueSize, Readers

(*--algorithm message_queue
variables queue = <<>>;

define 
    NoQueueOverflow == Len(queue) <= MaxQueueSize
end define;

procedure add_to_queue(val)
begin
    Add:
        queue := Append(queue, val);
        await Len(queue) <= MaxQueueSize;
        return;
end procedure;

process writer = "writer"
begin Write:
    while TRUE do
        call add_to_queue("msg");
    end while;
end process;

process reader \in Readers
variables current_msg = "";
begin Read:
    while TRUE do
        await queue /= <<>>;
        current_msg := Head(queue);
        queue := Tail(queue);
        either
            skip;
        or
            NotifyFailure:
                current_msg := "none";
                call add_to_queue(self);
        end either;
    end while;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES queue, pc, stack

(* define statement *)
NoQueueOverflow == Len(queue) <= MaxQueueSize

VARIABLES val, current_msg

vars == << queue, pc, stack, val, current_msg >>

ProcSet == {"writer"} \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<>>
        (* Procedure add_to_queue *)
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Process reader *)
        /\ current_msg = [self \in Readers |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self \in Readers -> "Read"]

Add(self) == /\ pc[self] = "Add"
             /\ queue' = Append(queue, val[self])
             /\ Len(queue') <= MaxQueueSize
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED current_msg

add_to_queue(self) == Add(self)

Write == /\ pc["writer"] = "Write"
         /\ /\ stack' = [stack EXCEPT !["writer"] = << [ procedure |->  "add_to_queue",
                                                         pc        |->  "Write",
                                                         val       |->  val["writer"] ] >>
                                                     \o stack["writer"]]
            /\ val' = [val EXCEPT !["writer"] = "msg"]
         /\ pc' = [pc EXCEPT !["writer"] = "Add"]
         /\ UNCHANGED << queue, current_msg >>

writer == Write

Read(self) == /\ pc[self] = "Read"
              /\ queue /= <<>>
              /\ current_msg' = [current_msg EXCEPT ![self] = Head(queue)]
              /\ queue' = Tail(queue)
              /\ \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Read"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "NotifyFailure"]
              /\ UNCHANGED << stack, val >>

NotifyFailure(self) == /\ pc[self] = "NotifyFailure"
                       /\ current_msg' = [current_msg EXCEPT ![self] = "none"]
                       /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "add_to_queue",
                                                                   pc        |->  "Read",
                                                                   val       |->  val[self] ] >>
                                                               \o stack[self]]
                          /\ val' = [val EXCEPT ![self] = self]
                       /\ pc' = [pc EXCEPT ![self] = "Add"]
                       /\ queue' = queue

reader(self) == Read(self) \/ NotifyFailure(self)

Next == writer
           \/ (\E self \in ProcSet: add_to_queue(self))
           \/ (\E self \in Readers: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Oct 01 12:05:45 EDT 2018 by john
\* Created Mon Oct 01 11:42:57 EDT 2018 by john
