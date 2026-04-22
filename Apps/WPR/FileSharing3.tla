------------- MODULE FileSharing3 ----------------

VARIABLES action, reactions

error == FALSE

CONSTANTS File, Token
VARIABLES accessible, trashed, urls, revoked, accessed

T == "Trash"
P == "Permalink"

Trash == INSTANCE Trash WITH Item <- File, Trash <- {T}
Permalink == INSTANCE Permalink WITH Permalink <- {P}, Resource <- File, URL <- Token

Actions == Trash!Actions \cup Permalink!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ Trash!Init
    /\ Permalink!Init

NextConcepts ==
    /\ Trash!Next
    /\ Permalink!Next

uploaded == accessible[T] \cup trashed[T]
shared == [ f \in File |-> urls[P][f] \ revoked[P] ]

Invariant ==
    /\ trashed[T] = {}
    /\ revoked[P] = accessed[P]
    /\ \A f \in File: f \in accessible[T] <=> shared[f] # {}
    /\ \A f \in File, x, y \in Token: x \in shared[f] /\ y \in shared[f] => x = y

(*
reaction create_share
when
	T.create[f]
then
	some t : Token | P.share[f,t]
*)

create_share_add == { <<"create_share", f>> : f \in { f \in File : Trash!create(T,f) } }
create_share_remove == { <<"create_share", f>> : f \in { f \in File : \E t \in Token : Permalink!share(P,f,t) } }

(*
reaction access_revoke
when
	P.access[t]
then
	P.revoke[t]
*)

access_revoke_add == { <<"access_revoke", t>> : t \in { t \in Token : Permalink!access(P,t) } }
access_revoke_remove == { <<"access_revoke", t>> : t \in { t \in Token : Permalink!revoke(P,t) } }

(*
reaction access_delete
when
	P.access[t]
where
	t in f.shared
then
	T.delete[f]
*)

access_delete_add == { <<"access_delete", f>> : f \in { f \in File : \E t \in Token : t \in shared[f] /\ Permalink!access(P,t) } }
access_delete_remove == { <<"access_delete", f>> : f \in { f \in File : Trash!delete(T,f) } }

(*
reaction access_empty
when
	P.access[t]
then
	T.empty[]
*)

access_empty_add == { <<"access_empty">> : x \in { x \in {<<>>} : \E t \in Token : Permalink!access(P,t) } }
access_empty_remove == { <<"access_empty">> : x \in { x \in {<<>>} : Trash!empty(T) } }

(*
reaction share_error
when
	P.share[f,t]
where
	f not in uploaded or some f.shared
then
	error
*)

share_error_add == { <<"share_error">> : x \in { x \in {<<>>} : \E f \in File, t \in Token : Permalink!share(P,f,t) /\ (f \notin uploaded \/ shared[f] # {}) } }
share_error_remove == { <<"share_error">> : x \in { x \in {<<>>} : error } }

(*
reaction delete_error
when
	T.delete[f]
where
	some f.shared and f.shared not in P.accessed
then
	error
*)

delete_error_add == { <<"delete_error">> : x \in { x \in {<<>>} : \E f \in File : Trash!delete(T,f) /\ shared[f] # {} /\ \A t \in shared[f] : t \notin accessed[P] } }
delete_error_remove == { <<"delete_error">> : x \in { x \in {<<>>} : error } }

(*
reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed  
then
	error
*)

revoke_error_add == { <<"revoke_error">> : x \in { x \in {<<>>} : \E t \in Token : Permalink!revoke(P,t) /\ t \notin accessed[P] } }
revoke_error_remove == { <<"revoke_error">> : x \in { x \in {<<>>} : error } }

\* Reaction semantics

reactions_to_add == create_share_add \cup access_revoke_add \cup access_delete_add \cup access_empty_add \cup share_error_add \cup delete_error_add \cup revoke_error_add
reactions_to_remove == create_share_remove \cup access_revoke_remove \cup access_delete_remove \cup access_empty_remove \cup share_error_remove \cup delete_error_remove \cup revoke_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

vars == <<accessible, trashed, urls, revoked, accessed, action, reactions>>

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

==================================================