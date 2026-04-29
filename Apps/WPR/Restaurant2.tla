-------- MODULE Restaurant2 --------

VARIABLES action, reactions

error == FALSE

CONSTANTS Client, Table, MaxTime

Restaurant == "Restaurant"
User == Client \cup {Restaurant}

VARIABLES available, reservations, time, inbox, outbox, reads

vars == <<action, reactions, available, reservations, time, inbox, outbox, reads>>

R == "Reservation"
M == "Messaging"

Reservation == INSTANCE Reservation WITH Reservation <- {R}, User <- Client, Resource <- Table
Messaging == INSTANCE Messaging WITH Messaging <- {M}, User <- User, Content <- Table

\* Only the restaurant can send messages, and only to clients
Message == { m \in Messaging!Message : m.from = Restaurant /\ m.to \in Client }

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
    \* A client has an active reservation for a table if and only if the restaurant has a confirmation message in the outbox.
    /\ \A c \in Client, t \in Table: (t \in active_reservations[c]) <=> (\E m \in Message: m.to = c /\ m.content = t /\ m \in outbox[M][Restaurant])
    \* There is at most one confirmation message for each table in the restaurant's outbox.
    /\ \A t \in Table, m1, m2 \in Message: m1.content = t /\ m1 \in outbox[M][Restaurant] /\ m2.content = t /\ m2 \in outbox[M][Restaurant] => m1 = m2

\* Reactions

(*
reaction send_confirmation
when
    R.reserve[c,t]
then
    some m : Message | M.send[Restaurant,m] and m.to = c and m.content = t
*)

send_confirmation_add == { <<r, c, t>> \in {"send_confirmation"} \X Client \X Table : Reservation!reserve(R,c,t) }
send_confirmation_remove == { <<r, c, t>> \in {"send_confirmation"} \X Client \X Table : \E m \in Message: Messaging!send(M,Restaurant,m) /\ m.to = c /\ m.content = t }

(*
reaction use_delete
when
    R.use[c,t]
then
    some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t
*)

use_delete_add == { <<r, c, t>> \in {"use_delete"} \X Client \X Table : Reservation!use(R,c,t) }
use_delete_remove == { <<r, c, t>> \in {"use_delete"} \X Client \X Table : \E m \in Message: Messaging!deleteFromOutbox(M,Restaurant,m) /\ m.to = c /\ m.content = t }

(*
reaction cancel_delete
when
    R.cancel[c,t]
then
    some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t
*)

cancel_delete_add == { <<r, c, t>> \in {"cancel_delete"} \X Client \X Table : Reservation!cancel(R,c,t) }
cancel_delete_remove == { <<r, c, t>> \in {"cancel_delete"} \X Client \X Table : \E m \in Message: Messaging!deleteFromOutbox(M,Restaurant,m) /\ m.to = c /\ m.content = t }

(*
reaction send_error
when
	M.send[Restaurant,m]
where
	m.content not in m.to.reservations or m.content in Restaurant.outbox.content
then
    error
*)

send_error_add == { <<r>> \in {<<"send_error">>} : \E m \in Message : Messaging!send(M,Restaurant,m) /\ (m.content \notin reservations[R][m.to] \/ \E m2 \in Message: m2.content = m.content /\ m2 \in outbox[M][Restaurant]) }
send_error_remove == { <<r>> \in {<<"send_error">>} : error }

(*
reaction delete_error
when
    M.deleteFromOutbox[Restaurant,m]
where
    m.content in m.to.reservations
then
    error
*)

delete_error_add == { <<r>> \in {<<"delete_error">>} : \E m \in Message : Messaging!deleteFromOutbox(M,Restaurant,m) /\ (m.content \in reservations[R][m.to]) }
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