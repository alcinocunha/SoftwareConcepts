-------------- MODULE Trash --------------

CONSTANT Trash, Item

VARIABLE accessible, trashed, occurred

Init ==
    /\ accessible = [ t \in Trash |-> {} ]
    /\ trashed = [ t \in Trash |-> {} ]
    /\ occurred = <<>>

create(t,i) ==
    /\ i \notin accessible[t]
    /\ i \notin trashed[t]
    /\ accessible' = [ accessible EXCEPT ![t] = @ \cup {i} ]
    /\ trashed' = trashed
    /\ occurred' = <<t, "create", i>>

delete(t,i) ==
    /\ i \in accessible[t]
    /\ accessible' = [ accessible EXCEPT ![t] = @ \ {i} ]
    /\ trashed' = [ trashed EXCEPT ![t] = @ \cup {i} ]
    /\ occurred' = <<t, "delete", i>>

restore(t,i) ==
    /\ i \in trashed[t]
    /\ accessible' = [ accessible EXCEPT ![t] = @ \cup {i} ]
    /\ trashed' = [ trashed EXCEPT ![t] = @ \ {i} ]
    /\ occurred' = <<t, "restore", i>>

empty(t) ==
    /\ trashed[t] # {}
    /\ accessible' = accessible
    /\ trashed' = [ trashed EXCEPT ![t] = {}]
    /\ occurred' = <<t, "empty">>

Next == 
    \/ \E t \in Trash, i \in Item: create(t, i)
    \/ \E t \in Trash, i \in Item: delete(t, i)
    \/ \E t \in Trash, i \in Item: restore(t, i)
    \/ \E t \in Trash: empty(t)

Spec == Init /\ [][Next]_<<accessible, trashed, occurred>>

Invariant == \A t \in Trash:
    /\ accessible[t] \cup trashed[t] \subseteq Item
    /\ accessible[t] \cap trashed[t] = {}

========================================