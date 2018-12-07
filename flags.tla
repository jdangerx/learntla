------------------------------- MODULE flags -------------------------------
EXTENDS Sequences

(* --algorithm flags
variables f1 \in {TRUE, FALSE}, f2 \in {TRUE, FALSE}, f3 \in {TRUE, FALSE};

define 
 ReverseTwo(tup) == IF Len(tup) = 2
                    THEN Append(Tail(tup), Head(tup))
                    ELSE tup
end define;

begin
    while TRUE do
        with n \in {1, 2, 3} do
            if n = 1 then
                either
                    f1 := TRUE;
                or
                    f1 := FALSE;
                end either;
            elsif n = 2 then
                either 
                    f2 := TRUE;
                or
                    f2 := FALSE;
                end either;
            else
                either
                    f3 := TRUE;
                or
                    f3 := FALSE;
                end either;            
            end if;
        end with;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES f1, f2, f3

(* define statement *)
ReverseTwo(tup) == IF Len(tup) = 2
                   THEN Append(Tail(tup), Head(tup))
                   ELSE tup


vars == << f1, f2, f3 >>

Init == (* Global variables *)
        /\ f1 \in {TRUE, FALSE}
        /\ f2 \in {TRUE, FALSE}
        /\ f3 \in {TRUE, FALSE}

Next == \E n \in {1, 2, 3}:
          IF n = 1
             THEN /\ \/ /\ f1' = TRUE
                     \/ /\ f1' = FALSE
                  /\ UNCHANGED << f2, f3 >>
             ELSE /\ IF n = 2
                        THEN /\ \/ /\ f2' = TRUE
                                \/ /\ f2' = FALSE
                             /\ f3' = f3
                        ELSE /\ \/ /\ f3' = TRUE
                                \/ /\ f3' = FALSE
                             /\ f2' = f2
                  /\ f1' = f1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Sep 25 14:14:26 EDT 2018 by john
\* Created Mon Sep 24 17:09:03 EDT 2018 by john
