-------------- MODULE ColoredFiles3 --------------

VARIABLES action, reactions

error == FALSE

CONSTANTS File, Color

ASSUME "Red" \in Color

VARIABLES accessible, trashed, labels

T == "Trash"
L == "Label"

Trash == INSTANCE Trash WITH Item <- File, Trash <- {T}
Label == INSTANCE Label WITH Item <- File, Tag <- Color, Label <- {L}

Actions == Trash!Actions \cup Label!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ Trash!Init
    /\ Label!Init

NextConcepts ==
    /\ Trash!Next
    /\ Label!Next

Invariant == 
    /\ \A f \in File: labels[L][f] # {} => f \in accessible[T] \/ f \in trashed[T]
    /\ \A f \in File: "Red" \in labels[L][f] <=> f \in trashed[T]

(*
reaction empty_clear
when
	T.empty()
where
	f in T.trashed
then
	L.clear(f)
*)

empty_clear_add == { <<r,f>> \in {"empty_clear"} \X File : Trash!empty(T) /\ f \in trashed[T] }
empty_clear_remove == { <<r,f>> \in {"empty_clear"} \X File : Label!clear(L,f) }

(*
reaction delete_affix
when
    T.delete(f)
then
    L.affix(f, "Red")
*)

delete_affix_add == { <<r,f>> \in {"delete_affix"} \X File : Trash!delete(T,f) }
delete_affix_remove == { <<r,f>> \in {"delete_affix"} \X File : Label!affix(L,f,"Red") }

(*
reaction restore_detach
when
    T.restore(f)
then
    L.detach(f, "Red")
*)

restore_detach_add == { <<r,f>> \in {"restore_detach"} \X File : Trash!restore(T,f) }
restore_detach_remove == { <<r,f>> \in {"restore_detach"} \X File : Label!detach(L,f,"Red") }

(*
reaction affix_error
when
	L.affix[f,c]
where
	f not in T.accessible and f not in T.trashed
then
	error
*)

affix_error_add == { <<r>> \in {<<"affix_error">>} : \E f \in File, c \in Color : Label!affix(L,f,c) /\ f \notin accessible[T] /\ f \notin trashed[T] }
affix_error_remove == { <<r>> \in {<<"affix_error">>} :  error }

(*
reaction affix_red_error
when
	L.affix[f,Red]
where
	f in T.accessible
then
	error
*)
affix_red_error_add == { <<r>> \in {<<"affix_red_error">>} : \E f \in File : Label!affix(L,f,"Red") /\ f \in accessible[T] }
affix_red_error_remove == { <<r>> \in {<<"affix_red_error">>} :  error }

(*
reaction detach_red_error
when
	L.detach[f,Red]
where
	f in T.trashed
then
	error
*)
detach_red_error_add == { <<r>> \in {<<"detach_red_error">>} : \E f \in File : Label!detach(L,f,"Red") /\ f \in trashed[T] }
detach_red_error_remove == { <<r>> \in {<<"detach_red_error">>} :  error }

(*
reaction clear_red_error
when
	L.clear[f]
where
	f in T.trashed and Red in f.colors
then
	error
*)

clear_red_error_add == { <<"clear_red_error">> : t \in { t \in {<<>>} : \E f \in File : Label!clear(L,f) /\ f \in trashed[T] /\ "Red" \in labels[L][f] } }
clear_red_error_remove == { <<"clear_red_error">> : t \in { t \in {<<>>} : error } }

\* Reaction semantics

reactions_to_add == empty_clear_add \cup delete_affix_add \cup restore_detach_add \cup affix_error_add \cup affix_red_error_add \cup detach_red_error_add \cup clear_red_error_add
reactions_to_remove == empty_clear_remove \cup delete_affix_remove \cup restore_detach_remove \cup affix_error_remove \cup affix_red_error_remove \cup detach_red_error_remove \cup clear_red_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

vars == <<accessible, trashed, labels, action, reactions>>

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

===============================================


