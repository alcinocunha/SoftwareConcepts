------------- MODULE Restaurant1 -------------

VARIABLES action, reactions

error == FALSE

CONSTANTS Client, Table

Reserved == "Reserved"

VARIABLES available, reservations, labels

vars == <<action, reactions, available, reservations, labels>>

R == "Reservation"
L == "Label"

Reservation == INSTANCE Reservation WITH Reservation <- {R}, User <- Client, Resource <- Table
Label == INSTANCE Label WITH Label <- {L}, Item <- Table, Tag <- {Reserved}

Actions == Reservation!Actions \cup Label!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ Reservation!Init
    /\ Label!Init

NextConcepts ==
    /\ Reservation!Next
    /\ Label!Next

tables == available[R]
active_reservations == [ u \in Client |-> reservations[R][u] \cap tables ]
reserved == { t \in Table : labels[L][t] # {} }

Invariant == reserved = { t \in Table : \E u \in Client : t \in active_reservations[u] }

(*
reaction reserve_affix
when
	R.reserve[c,t]
then
	L.affix[t,Reserved]
*)

reserve_affix_add == { <<"reserve_affix", t>> : t \in { t \in Table : \E c \in Client : Reservation!reserve(R,c,t) } }
reserve_affix_remove == { <<"reserve_affix", t>> : t \in { t \in Table : Label!affix(L,t,Reserved) } }

(*
reaction cancel_detach
when
	R.cancel[c,t]
then
	L.detach[t,Reserved] or L.clear[t]
*)

cancel_detach_add == { <<"cancel_detach", t>> : t \in { t \in Table : \E c \in Client : Reservation!cancel(R,c,t) } }
cancel_detach_remove == { <<"cancel_detach", t>> : t \in { t \in Table : Label!detach(L,t,Reserved) \/ Label!clear(L,t) } }

(*
reaction use_detach
when
	R.use[c,t]
then
	L.detach[t,Reserved] or L.clear[t]
*)

use_detach_add == { <<"use_detach", t>> : t \in { t \in Table : \E c \in Client : Reservation!use(R,c,t) } }
use_detach_remove == { <<"use_detach", t>> : t \in { t \in Table : Label!detach(L,t,Reserved) \/ Label!clear(L,t) } }

(*
reaction affix_error
when
	L.affix[t,Reserved]
where
	t not in Client.active_reservations
then
	error
*)

affix_error_add == { <<"affix_error">> : x \in { x \in {<<>>} : \E t \in Table : Label!affix(L,t,Reserved) /\ \A c \in Client : t \notin active_reservations[c] } }
affix_error_remove == { <<"affix_error">> : t \in { t \in {<<>>} : error } }

(*
reaction detach_error
when
	L.detach[t,Reserved]
where
	t in Client.active_reservations
then
	error
*)

detach_error_add == { <<"detach_error">> : x \in { x \in {<<>>} : \E t \in Table : Label!detach(L,t,Reserved) /\ \E c \in Client : t \in active_reservations[c] } }
detach_error_remove == { <<"detach_error">> : t \in { t \in {<<>>} : error } }

(*
reaction clear_error
when
	L.clear[t]
where
	t in Client.active_reservations
then
	error
*)

clear_error_add == { <<"clear_error">> : x \in { x \in {<<>>} : \E t \in Table : Label!clear(L,t) /\ \E c \in Client : t \in active_reservations[c] } }
clear_error_remove == { <<"clear_error">> : t \in { t \in {<<>>} : error } }

\* Reaction semantics

reactions_to_add == reserve_affix_add \cup cancel_detach_add \cup use_detach_add \cup affix_error_add \cup detach_error_add \cup clear_error_add
reactions_to_remove == reserve_affix_remove \cup cancel_detach_remove \cup use_detach_remove \cup affix_error_remove \cup detach_error_remove \cup clear_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

==============================================