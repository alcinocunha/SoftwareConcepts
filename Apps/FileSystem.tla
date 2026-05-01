-------- MODULE FileSystem --------

EXTENDS Naturals, TLC, FiniteSets

VARIABLES action, reactions

error == FALSE

CONSTANTS Other, File, Dir

ASSUME File \cap Dir = {}

Object == File \cup Dir

Symmetry == Permutations(Other) \cup Permutations(File) \cup Permutations(Dir)

VARIABLES accessible, trashed, owns

Root == "Root"
O == "Owning"

Trash == Other \cup {Root}

TRASH == INSTANCE Trash WITH Item <- Object
OWNING == INSTANCE Owning WITH Owning <- {O}, User <- Dir, Resource <- Trash

content == owns[O]

Actions == TRASH!Actions \cup OWNING!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ TRASH!Init
    /\ OWNING!Init

NextConcepts ==
    /\ TRASH!Next
    /\ OWNING!Next

children(d) == { o \in Object: d \in Dir /\ \E t \in Trash: t \in content[d] /\ (o \in accessible[t] \/ o \in trashed[t]) }

reachable(d) ==
  LET rch[i \in Nat] == IF i = 1 THEN children(d)
                        ELSE rch[i-1] \cup { x \in Object : \E y \in rch[i-1] : x \in children(y) }
  IN  rch[Cardinality(Object)]

Invariant ==
    \* The non root trashes have objects if they are owned by some directory
    /\ \A t \in Other: (accessible[t] # {} \/ trashed[t] # {}) => \E d \in Dir: t \in content[d]
    \* A directory owns a trash iff it is in some trash
    /\ \A d \in Dir: content[d] # {} <=> \E t \in Trash: d \in accessible[t] \/ d \in trashed[t]
    \* A directory can only be in one trash and can only contain one trash
    /\ \A d \in Dir: \A t1,t2 \in Trash: (d \in accessible[t1] \/ d \in trashed[t1]) /\ (d \in accessible[t2] \/ d \in trashed[t2]) => t1 = t2
    /\ \A d \in Dir: \A t1,t2 \in Trash: t1 \in content[d] /\ t2 \in content[d] => t1 = t2
    \* No cycles
    /\ \A d \in Dir: d \notin reachable(d)

\* Reactions

(*
reaction create_dir
when 
    t.create(d)
where
    d in Dir
then
    some t : Other | O.acquire(d,t)
*)

create_dir_add == { <<r,d>> \in {"create_dir"} \X Dir : \E t \in Trash: TRASH!create(t,d) }
create_dir_remove == { <<r,d>> \in {"create_dir"} \X Dir : \E t \in Trash: OWNING!acquire(O,d,t) }

(*
reaction empty_dir
when
    t.empty()
where
    d in t.trashed and x in d.content
then
    O.release(d,x)
*)

empty_dir_add == { <<r,d,x>> \in {"empty_dir"} \X Dir \X Trash : \E t \in Trash: TRASH!empty(t) /\ d \in trashed[t] /\ x \in content[d] }
empty_dir_remove == { <<r,d,x>> \in {"empty_dir"} \X Dir \X Trash : OWNING!release(O,d,x) }

(*
reaction release_trash_delete_objects
when
    O.release(d,t)
where
    o in t.accessible
then
    t.delete(o)
*)

release_trash_delete_objects_add == { <<r,t,o>> \in {"release_trash_delete_objects"} \X Trash \X Object : \E d \in Dir: OWNING!release(O,d,t) /\ o \in accessible[t] }
release_trash_delete_objects_remove == { <<r,t,o>> \in {"release_trash_delete_objects"} \X Trash \X Object : TRASH!delete(t,o) }

(*
reaction release_trash_empty
when
    O.release(d,t)
where
    no t.accessible and some t.trashed
then
    t.empty()
*)

release_trash_empty_add == { <<r,t>> \in {"release_trash_empty"} \X Trash : \E d \in Dir: OWNING!release(O,d,t) /\ accessible[t] = {} /\ trashed[t] # {} }
release_trash_empty_remove == { <<r,t>> \in {"release_trash_empty"} \X Trash : TRASH!empty(t) }

(*
reaction delete_last_empty
when
    t.delete(o)
where
    t not in Root and no content.t and t.accessible in o
then
    t.empty()
*)

delete_last_empty_add == { <<r,t>> \in {"delete_last_empty"} \X Trash : \E o \in Object: TRASH!delete(t,o) /\ t # Root /\ (\A d \in Dir: t \notin content[d]) /\ accessible[t] = {o} }
delete_last_empty_remove == { <<r,t>> \in {"delete_last_empty"} \X Trash : TRASH!empty(t) }

(*
reaction acquire_error
when
    O.acquire(o,t)
where
    o in File or no (accessible+trashed).o or some o.content or some t.(accessible+trashed)
then
    error
*)

acquire_error_add == { <<r>> \in {<<"acquire_error">>} : \E o \in Object, t \in Trash : OWNING!acquire(O,o,t) /\ (o \in File \/ (\A x \in Trash: o \notin accessible[x] /\ o \notin trashed[x]) \/ content[o] # {} \/ accessible[t] # {} \/ trashed[t] # {}) }
acquire_error_remove == { <<r>> \in {<<"acquire_error">>} : error } 

(*
reaction create_error
when
    t.create(o)
where
    t not in Root and no content.t
then
    error
*)

create_error_add == { <<r>> \in {<<"create_error">>} : \E t \in Trash, o \in Object : TRASH!create(t,o) /\ t # Root /\ (\A d \in Dir: t \notin content[d]) }
create_error_remove == { <<r>> \in {<<"create_error">>} : error }

(*
reaction release_error
when
    O.release(d,t)
where
    some (accessible+trashed).d
then
    error
*)

release_error_add == { <<r>> \in {<<"release_error">>} : \E d \in Dir, t \in Trash : OWNING!release(O,d,t) /\ (\E x \in Trash : d \in accessible[x] \/ d \in trashed[x]) }
release_error_remove == { <<r>> \in {<<"release_error">>} : error }

\* Reaction semantics

reactions_to_add == create_dir_add \cup empty_dir_add \cup release_trash_delete_objects_add \cup release_trash_empty_add \cup delete_last_empty_add \cup acquire_error_add \cup create_error_add \cup release_error_add
reactions_to_remove == create_dir_remove \cup empty_dir_remove \cup release_trash_delete_objects_remove \cup release_trash_empty_remove \cup delete_last_empty_remove \cup acquire_error_remove \cup create_error_remove \cup release_error_remove

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

vars == <<accessible, trashed, owns, action, reactions>>

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

===================================