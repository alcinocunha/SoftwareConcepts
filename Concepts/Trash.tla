-------------- MODULE Trash --------------

CONSTANT Trash, Item

VARIABLE accessible, trashed, action

Actions == Trash \X {"create", "delete", "restore"} \X Item \cup Trash \X {"empty"}

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ accessible = [ t \in Trash |-> {} ]
    /\ trashed = [ t \in Trash |-> {} ]

create(t,i) ==
    /\ action = <<t, "create", i>>
    /\ i \notin accessible[t]
    /\ i \notin trashed[t]
    /\ accessible' = [ accessible EXCEPT ![t] = @ \cup {i} ]
    /\ trashed' = trashed

delete(t,i) ==
    /\ action = <<t, "delete", i>>
    /\ i \in accessible[t]
    /\ accessible' = [ accessible EXCEPT ![t] = @ \ {i} ]
    /\ trashed' = [ trashed EXCEPT ![t] = @ \cup {i} ]

restore(t,i) ==
    /\ action = <<t, "restore", i>>
    /\ i \in trashed[t]
    /\ accessible' = [ accessible EXCEPT ![t] = @ \cup {i} ]
    /\ trashed' = [ trashed EXCEPT ![t] = @ \ {i} ]

empty(t) ==
    /\ action = <<t, "empty">>
    /\ trashed[t] # {}
    /\ accessible' = accessible
    /\ trashed' = [ trashed EXCEPT ![t] = {}]

stutter(t) ==
    /\ action[1] # t
    /\ accessible' = accessible
    /\ trashed' = trashed

Next == \E t \in Trash:
    \/ \E i \in Item: create(t, i)
    \/ \E i \in Item: delete(t, i)
    \/ \E i \in Item: restore(t, i)
    \/ empty(t)
    \/ stutter(t)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<accessible, trashed, action>>

Invariant == \A t \in Trash:
    /\ accessible[t] \cup trashed[t] \subseteq Item
    /\ accessible[t] \cap trashed[t] = {}

========================================