------------------------------ MODULE library ------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANT Books
CONSTANT People
CONSTANT NumCopies

ASSUME NumCopies \subseteq Nat

PT == INSTANCE PT

set ++ element == set \union {element}
set -- element == set \ {element}

ReduceFunVals(op(_, _), fun, acc) ==
  PT!ReduceSet(LAMBDA i, a: op(fun[i], a), DOMAIN fun, acc)
  
SumFun(fun) == ReduceFunVals(+, fun, 0)
  
(*--algorithm library
variable
  library \in [Books -> NumCopies],
  reserved = [b \in Books |-> <<>>],
  total_books = SumFun(library);
  
define
  AvailableBooks == {b \in DOMAIN library: library[b] > 0}
  BorrowableBooks(p) ==
    {b \in AvailableBooks: 
      \/ reserved[b] = <<>> 
      \/ p = Head(reserved[b])
    }
end define;
  
fair process person \in People
variables books = {}, wants \in SUBSET Books;
begin
  Person:
  either
    with book \in (BorrowableBooks(self) \intersect wants) \ books do \* checkout
      books := books ++ book;
      wants := wants -- book;
      library[book] := library[book] - 1;
      if reserved[book] /= <<>> /\ self = Head(reserved[book])
      then reserved[book] := Tail(reserved[book]);  
      end if;  
    end with;
  or
    with book \in books do \* return
      books := books -- book;
      library[book] := library[book] + 1;
    end with;
  or
    with book \in {b \in wants: self \notin PT!Range(reserved[b])} do \* reserve
      reserved[book] := Append(reserved[book], self);
    end with;
  or
    await wants = {}; \* want
    with some_books \in SUBSET Books do
      wants := some_books;
    end with;
  end either;
  goto Person;
end process;

fair process book_reservations \in Books
begin
  Expire:
    await reserved[self] /= <<>>;
    reserved[self] := Tail(reserved[self]);
  goto Expire;
end process;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES library, reserved, total_books, pc

(* define statement *)
AvailableBooks == {b \in DOMAIN library: library[b] > 0}
BorrowableBooks(p) ==
  {b \in AvailableBooks:
    \/ reserved[b] = <<>>
    \/ p = Head(reserved[b])
  }

VARIABLES books, wants

vars == << library, reserved, total_books, pc, books, wants >>

ProcSet == (People) \cup (Books)

Init == (* Global variables *)
        /\ library \in [Books -> NumCopies]
        /\ reserved = [b \in Books |-> <<>>]
        /\ total_books = SumFun(library)
        (* Process person *)
        /\ books = [self \in People |-> {}]
        /\ wants \in [People -> SUBSET Books]
        /\ pc = [self \in ProcSet |-> CASE self \in People -> "Person"
                                        [] self \in Books -> "Expire"]

Person(self) == /\ pc[self] = "Person"
                /\ \/ /\ \E book \in (BorrowableBooks(self) \intersect wants[self]) \ books[self]:
                           /\ books' = [books EXCEPT ![self] = books[self] ++ book]
                           /\ wants' = [wants EXCEPT ![self] = wants[self] -- book]
                           /\ library' = [library EXCEPT ![book] = library[book] - 1]
                           /\ IF reserved[book] /= <<>> /\ self = Head(reserved[book])
                                 THEN /\ reserved' = [reserved EXCEPT ![book] = Tail(reserved[book])]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED reserved
                   \/ /\ \E book \in books[self]:
                           /\ books' = [books EXCEPT ![self] = books[self] -- book]
                           /\ library' = [library EXCEPT ![book] = library[book] + 1]
                      /\ UNCHANGED <<reserved, wants>>
                   \/ /\ \E book \in {b \in wants[self]: self \notin PT!Range(reserved[b])}:
                           reserved' = [reserved EXCEPT ![book] = Append(reserved[book], self)]
                      /\ UNCHANGED <<library, books, wants>>
                   \/ /\ wants[self] = {}
                      /\ \E some_books \in SUBSET Books:
                           wants' = [wants EXCEPT ![self] = some_books]
                      /\ UNCHANGED <<library, reserved, books>>
                /\ pc' = [pc EXCEPT ![self] = "Person"]
                /\ UNCHANGED total_books

person(self) == Person(self)

Expire(self) == /\ pc[self] = "Expire"
                /\ reserved[self] /= <<>>
                /\ reserved' = [reserved EXCEPT ![self] = Tail(reserved[self])]
                /\ pc' = [pc EXCEPT ![self] = "Expire"]
                /\ UNCHANGED << library, total_books, books, wants >>

book_reservations(self) == Expire(self)

Next == (\E self \in People: person(self))
           \/ (\E self \in Books: book_reservations(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in People : WF_vars(person(self))
        /\ \A self \in Books : WF_vars(book_reservations(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

ConservationOfBooks ==
  LET
    num_available == SumFun(library)
    num_checked_out == ReduceFunVals(
      LAMBDA personal_books, acc: Cardinality(personal_books) + acc,
      books,
      0)
  IN
    num_available + num_checked_out = total_books
    
NoDuplicateReservations ==
  \A b \in Books:
    \A i, j \in 1..Len(reserved[b]):
      i /= j => reserved[b][i] /= reserved[b][j]

TypeInvariant ==
  /\ ConservationOfBooks
  /\ library \in [Books -> NumCopies ++ 0]
  /\ books \in [People -> SUBSET Books]
  /\ wants \in [People -> SUBSET Books]
  /\ reserved \in [Books -> Seq(People)]
  /\ NoDuplicateReservations
  
NextInLineFor(p, b) ==
  /\ reserved[b] /= <<>>
  /\ Head(reserved[b]) = p

WishFulfillment == 
  \A p \in People:
    \A b \in Books:
      b \in wants[p] ~>
        \/ b \notin wants[p]
        \/ NextInLineFor(p, b) 

=============================================================================
\* Modification History
\* Last modified Wed Oct 31 11:56:37 EDT 2018 by john
\* Created Mon Oct 29 17:17:20 EDT 2018 by john
