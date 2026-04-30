-------- MODULE Messaging --------

EXTENDS Naturals, TLC

CONSTANTS Messaging, User, Content, MaxTime

ASSUME MaxTime \in Nat

Time == 0..MaxTime

Symmetry == Permutations(User) \cup Permutations(Content)

VARIABLES action, time, inbox, outbox, reads

Message == [ from: User, to: User, content: Content, when : Time ]

TypeOK ==
    /\ time \in Time
    /\ inbox  \in [ Messaging -> [ User -> SUBSET Message ] ]
    /\ outbox \in [ Messaging -> [ User -> SUBSET Message ] ]
    /\ reads  \in [ Messaging -> [ User -> SUBSET Message ] ]

Actions == Messaging \X {"read", "deleteFromInbox", "deleteFromOutbox"} \X User \X Message \cup Messaging \X {"send"} \X User \X User \X Content

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ time = 0
    /\ inbox = [ m \in Messaging |-> [ u \in User |-> {} ] ]
    /\ outbox = [ m \in Messaging |-> [ u \in User |-> {} ] ]
    /\ reads = [ m \in Messaging |-> [ u \in User |-> {} ] ]

send(c,u,t,x) == 
    /\ action = <<c, "send", u, t, x>>
    /\ time < MaxTime
    /\ outbox' = [ outbox EXCEPT ![c][u] = @ \cup {[from |-> u, to |-> t, content |-> x, when |-> time]} ]
    /\ inbox' = [ inbox EXCEPT ![c][t] = @ \cup {[from |-> u, to |-> t, content |-> x, when |-> time]} ]
    /\ time' = time + 1
    /\ UNCHANGED reads

read(c,u,m) ==
    /\ action = <<c, "read", u, m>>
    /\ m \in inbox[c][u]
    /\ m \notin reads[c][u]
    /\ reads' = [ reads EXCEPT ![c][u] = @ \cup {m} ]
    /\ UNCHANGED <<inbox, outbox, time>>

deleteFromInbox(c,u,m) ==
    /\ action = <<c, "deleteFromInbox", u, m>>
    /\ m \in inbox[c][u]
    /\ inbox' = [ inbox EXCEPT ![c][u] = @ \ {m} ]
    /\ reads' = [ reads EXCEPT ![c][u] = @ \ {m} ]
    /\ UNCHANGED <<outbox, time>>

deleteFromOutbox(c,u,m) ==
    /\ action = <<c, "deleteFromOutbox", u, m>>
    /\ m \in outbox[c][u]
    /\ outbox' = [ outbox EXCEPT ![c][u] = @ \ {m} ]
    /\ UNCHANGED <<inbox, reads, time>>

stutter(c) ==
    /\ action[1] # c
    /\ UNCHANGED <<time, inbox, outbox, reads>>

Next == \E c \in Messaging:
    \/ \E u,t \in User: \E x \in Content: send(c,u,t,x)
    \/ \E u \in User: \E m \in inbox[c][u]: read(c,u,m)
    \/ \E u \in User: \E m \in inbox[c][u]: deleteFromInbox(c,u,m)
    \/ \E u \in User: \E m \in outbox[c][u]: deleteFromOutbox(c,u,m)
    \/ stutter(c)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<action, time, inbox, outbox, reads>>

Invariant == \A c \in Messaging:
    \* The messages read by each user are in their inbox
    /\ \A u \in User: reads[c][u] \subseteq inbox[c][u]
    \* The messages in the outbox are from the user
    /\ \A u \in User, m \in Message: m \in outbox[c][u] => m.from = u
    \* The messages in the inbox are to the user
    /\ \A u \in User, m \in Message: m \in inbox[c][u] => m.to = u
    \* All messages in inboxes and outboxes have a time stamp that is strictly anterior to the current time
    /\ \A u \in User, m \in Message: m \in inbox[c][u] \/ m \in outbox[c][u] => m.when < time
    \* There is at most one message in the outbox of each user with a given time stamp
    /\ \A u \in User, m1, m2 \in Message: m1 \in outbox[c][u] /\ m2 \in outbox[c][u] /\ m1.when = m2.when => m1 = m2
    \* There is at most one message in the inbox of each user with a given time stamp    
    /\ \A u \in User, m1, m2 \in Message: m1 \in inbox[c][u] /\ m2 \in inbox[c][u] /\ m1.when = m2.when => m1 = m2

=============================