-------------- MODULE ColoredFiles1 --------------

VARIABLES action, reactions

error == FALSE

CONSTANTS File, Color

VARIABLES accessible, trashed, labels

T == "Trash"
L == "Label"

Trash == INSTANCE Trash WITH Item <- File, Trash <- {T}
Label == INSTANCE Label WITH Item <- File, Tag <- Color, Label <- {L}

colors == labels[L]

Actions == Trash!Actions \cup Label!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ Trash!Init
    /\ Label!Init

NextConcepts ==
    /\ Trash!Next
    /\ Label!Next

Invariant == { f \in File : colors[f] # {} } \subseteq accessible[T]

(*
reaction delete_clear
when
	T.delete[f]
where
	some f.colors
then
	L.clear[f]
*)

delete_clear_add == { <<r,f>> \in {"delete_clear"} \X File : Trash!delete(T,f) /\ colors[f] # {} }
delete_clear_remove == { <<r,f>> \in {"delete_clear"} \X File : Label!clear(L,f) }

(*
reaction affix_error
when
	L.affix[f,c]
where
	f not in T.accessible
then
	error
*)

affix_error_add == { <<r>> \in {<<"affix_error">>} : \E f \in File, c \in Color : Label!affix(L,f,c) /\ f \notin accessible[T] }
affix_error_remove == { <<r>> \in {<<"affix_error">>} :  error }

\* Reaction semantics

reactions_to_add == delete_clear_add \cup affix_error_add
reactions_to_remove == delete_clear_remove \cup affix_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

vars == <<accessible, trashed, labels, action, reactions>>

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

===============================================


