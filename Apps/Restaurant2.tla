-------- MODULE Restaurant2 --------

EXTENDS TLC

VARIABLES action, reactions

error == FALSE

CONSTANTS Client, Table, MaxTime

Restaurant == "Restaurant"
User == Client \cup {Restaurant}

Symmetry == Permutations(Client) \cup Permutations(Table)

VARIABLES available, reservations, time, inbox, outbox, reads

vars == <<action, reactions, available, reservations, time, inbox, outbox, reads>>

R == "Reservation"
M == "Messaging"

Reservation == INSTANCE Reservation WITH Reservation <- {R}, User <- Client, Resource <- Table
Messaging == INSTANCE Messaging WITH Messaging <- {M}, User <- User, Content <- Table

\* Only the restaurant can send messages
Message == { m \in Messaging!Message : m.from = Restaurant }

Actions == Reservation!Actions \cup Messaging!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ Reservation!Init
    /\ Messaging!Init

NextConcepts ==
    /\ Reservation!Next
    /\ Messaging!Next

tables == available[R]
active_reservations == [ u \in Client |-> reservations[R][u] \cap tables ]

Invariant ==
    \* A user has an active reservation for a table if and only if the restaurant has a confirmation message in the outbox.
    /\ \A c \in User, t \in Table: (c \in Client /\ t \in active_reservations[c]) <=> (\E m \in Message: m.to = c /\ m.content = t /\ m \in outbox[M][Restaurant])
    \* There is at most one confirmation message for each table in the restaurant's outbox.
    /\ \A t \in Table, m1, m2 \in Message: m1.content = t /\ m1 \in outbox[M][Restaurant] /\ m2.content = t /\ m2 \in outbox[M][Restaurant] => m1 = m2

\* Reactions

(*
reaction send_confirmation
when
    R.reserve[c,t]
then
    M.send[Restaurant,c,t]
*)

send_confirmation_add == { <<r, c, t>> \in {"send_confirmation"} \X Client \X Table : Reservation!reserve(R,c,t) }
send_confirmation_remove == { <<r, c, t>> \in {"send_confirmation"} \X Client \X Table : Messaging!send(M,Restaurant,c,t) }

(*
reaction use_delete
when
    R.use[c,t]
where
    m in M.outbox[Restaurant] and m.to = c and m.content = t
then
    M.deleteFromOutbox[Restaurant,m]
*)

use_delete_add == { <<r, m>> \in {"use_delete"} \X Message : \E c \in Client, t \in Table : Reservation!use(R,c,t) /\ m \in outbox[M][Restaurant] /\ m.to = c /\ m.content = t }
use_delete_remove == { <<r, m>> \in {"use_delete"} \X Message : Messaging!deleteFromOutbox(M,Restaurant,m) }

(*
reaction cancel_delete
when
    R.cancel[c,t]
where
    m in M.outbox[Restaurant] and m.to = c and m.content = t
then
    M.deleteFromOutbox[Restaurant,m]
*)

cancel_delete_add == { <<r, m>> \in {"cancel_delete"} \X Message : \E c \in Client, t \in Table : Reservation!cancel(R,c,t) /\ m \in outbox[M][Restaurant] /\ m.to = c /\ m.content = t }
cancel_delete_remove == { <<r, m>> \in {"cancel_delete"} \X Message : Messaging!deleteFromOutbox(M,Restaurant,m) }

(*
reaction send_error
when
	M.send[Restaurant,u,t]
where
	t not in u.active_reservations or t in Restaurant.outbox.content
then
    error
*)

send_error_add == { <<r>> \in {<<"send_error">>} : \E u \in User, t \in Table : Messaging!send(M,Restaurant,u,t) /\ (u \notin DOMAIN active_reservations \/ t \notin active_reservations[u] \/ \E m2 \in Message: m2.content = t /\ m2 \in outbox[M][Restaurant]) }
send_error_remove == { <<r>> \in {<<"send_error">>} : error }

(*
reaction delete_error
when
    M.deleteFromOutbox[Restaurant,m]
where
    m.content in m.to.active_reservations
then
    error
*)

delete_error_add == { <<r>> \in {<<"delete_error">>} : \E m \in Message : Messaging!deleteFromOutbox(M,Restaurant,m) /\ (m.content \in active_reservations[m.to]) }
delete_error_remove == { <<r>> \in {<<"delete_error">>} : error }

\* Reaction semantics

reactions_to_add == send_confirmation_add \cup use_delete_add \cup cancel_delete_add \cup send_error_add \cup delete_error_add
reactions_to_remove == send_confirmation_remove \cup use_delete_remove \cup cancel_delete_remove \cup send_error_remove \cup delete_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

====================================