------------------------------ MODULE database ------------------------------
EXTENDS TLC
CONSTANT Data, Clients, NULL


(*--algorithm database
variables
  query = [c \in Clients |-> NULL],
  ghost_db_val_at_request_time = [c \in Clients |-> NULL];
  
define
  Exists(val) == val /= NULL
  RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;
  
macro request(data) begin
  query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
  await query[self].type = "response";
end macro;

process client \in Clients
variable result = NULL;
begin
  Request:
  while TRUE do
    either
      request([op |-> "read"]);
      Confirm:
        wait_for_response();
        result := query[self].result;
        assert result = ghost_db_val_at_request_time[self];
    or
      with d \in Data do
        request([op |-> "write", data |-> d]);
      end with;
      Wait:
        wait_for_response();
    end either;
  end while;
end process;

process database = "Database"
variables db_value \in Data;
begin
  Database:
  while TRUE do
    with c \in RequestingClients, q = query[c] do
      if q.op = "write" then
        db_value := q.data;
      elsif q.op = "read" then
        skip;
      else
        assert FALSE;
      end if;
      ghost_db_val_at_request_time[c] := db_value;
      query[c] := [type |-> "response", result |-> db_value];
    end with;    
  end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES query, ghost_db_val_at_request_time, pc

(* define statement *)
Exists(val) == val /= NULL
RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}

VARIABLES result, db_value

vars == << query, ghost_db_val_at_request_time, pc, result, db_value >>

ProcSet == (Clients) \cup {"Database"}

Init == (* Global variables *)
        /\ query = [c \in Clients |-> NULL]
        /\ ghost_db_val_at_request_time = [c \in Clients |-> NULL]
        (* Process client *)
        /\ result = [self \in Clients |-> NULL]
        (* Process database *)
        /\ db_value \in Data
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "Request"
                                        [] self = "Database" -> "Database"]

Request(self) == /\ pc[self] = "Request"
                 /\ \/ /\ query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([op |-> "read"])]
                       /\ pc' = [pc EXCEPT ![self] = "Confirm"]
                    \/ /\ \E d \in Data:
                            query' = [query EXCEPT ![self] = [type |-> "request"] @@ ([op |-> "write", data |-> d])]
                       /\ pc' = [pc EXCEPT ![self] = "Wait"]
                 /\ UNCHANGED << ghost_db_val_at_request_time, result, 
                                 db_value >>

Confirm(self) == /\ pc[self] = "Confirm"
                 /\ query[self].type = "response"
                 /\ result' = [result EXCEPT ![self] = query[self].result]
                 /\ Assert(result'[self] = ghost_db_val_at_request_time[self], 
                           "Failure of assertion at line 34, column 9.")
                 /\ pc' = [pc EXCEPT ![self] = "Request"]
                 /\ UNCHANGED << query, ghost_db_val_at_request_time, db_value >>

Wait(self) == /\ pc[self] = "Wait"
              /\ query[self].type = "response"
              /\ pc' = [pc EXCEPT ![self] = "Request"]
              /\ UNCHANGED << query, ghost_db_val_at_request_time, result, 
                              db_value >>

client(self) == Request(self) \/ Confirm(self) \/ Wait(self)

Database == /\ pc["Database"] = "Database"
            /\ \E c \in RequestingClients:
                 LET q == query[c] IN
                   /\ IF q.op = "write"
                         THEN /\ db_value' = q.data
                         ELSE /\ IF q.op = "read"
                                    THEN /\ TRUE
                                    ELSE /\ Assert(FALSE, 
                                                   "Failure of assertion at line 56, column 9.")
                              /\ UNCHANGED db_value
                   /\ ghost_db_val_at_request_time' = [ghost_db_val_at_request_time EXCEPT ![c] = db_value']
                   /\ query' = [query EXCEPT ![c] = [type |-> "response", result |-> db_value']]
            /\ pc' = [pc EXCEPT !["Database"] = "Database"]
            /\ UNCHANGED result

database == Database

Next == database
           \/ (\E self \in Clients: client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Oct 29 16:49:25 EDT 2018 by john
\* Created Fri Oct 26 15:20:48 EDT 2018 by john
