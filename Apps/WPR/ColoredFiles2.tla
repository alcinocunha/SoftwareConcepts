-------------- MODULE ColoredFiles2 --------------

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

Invariant == { f \in File : colors[f] # {} } \subseteq accessible[T] \cup trashed[T]

(*
reaction empty_clear
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f]
*)

empty_clear_add == { <<"empty_clear", f>> : f \in { f \in File : Trash!empty(T) /\ f \in trashed[T] /\ colors[f] # {} } }
empty_clear_remove == { <<"empty_clear", f>> : f \in { f \in File : Label!clear(L,f) } }

(*
reaction affix_error
when
	L.affix[f,c]
where
	f not in T.accessible and f not in T.trashed
then
	error
*)

affix_error_add == { <<"affix_error">> : t \in { t \in {<<>>} : \E f \in File, c \in Color : Label!affix(L,f,c) /\ f \notin accessible[T] /\ f \notin trashed[T] } }
affix_error_remove == { <<"affix_error">> : t \in { t \in {<<>>} : error } }

\* Reaction semantics

reactions_to_add == empty_clear_add \cup affix_error_add
reactions_to_remove == empty_clear_remove \cup affix_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

vars == <<accessible, trashed, labels, action, reactions>>

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

===============================================


