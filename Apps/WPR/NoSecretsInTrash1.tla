-------------- MODULE NoSecretsInTrash1 --------------

VARIABLES action, reactions

error == FALSE

CONSTANTS File, Secret

ASSUME Secret \subseteq File

VARIABLES accessible, trashed

T == "Trash"

Trash == INSTANCE Trash WITH Item <- File, Trash <- {T}

Actions == Trash!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts == Trash!Init

NextConcepts == Trash!Next
 
Invariant == \A f \in trashed[T] : f \notin Secret

(*
reaction delete_empty
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]
*)

delete_empty_add == { <<"delete_empty">> : x \in { x \in {<<>>} : \E f \in File: Trash!delete(T,f) /\ f \in Secret } }
delete_empty_remove == { <<"delete_empty">> : x \in { x \in {<<>>} : Trash!empty(T) } }

\* Reaction semantics

reactions_to_add == delete_empty_add
reactions_to_remove == delete_empty_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

vars == <<accessible, trashed, action, reactions>>

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

===============================================


