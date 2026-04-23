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

Actions == Messaging \X {"send", "read", "deleteFromInbox", "deleteFromOutbox"} \X User \X Message

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ time = 0
    /\ inbox = [ m \in Messaging |-> [ u \in User |-> {} ] ]
    /\ outbox = [ m \in Messaging |-> [ u \in User |-> {} ] ]
    /\ reads = [ m \in Messaging |-> [ u \in User |-> {} ] ]

send(c,u,m) == 
    /\ action = <<c, "send", u, m>>
    /\ time < MaxTime
    /\ m.from = u
    /\ m.when = time
    /\ outbox' = [ outbox EXCEPT ![c][u] = @ \cup {m} ]
    /\ inbox' = [ inbox EXCEPT ![c][m.to] = @ \cup {m} ]
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
    \/ \E u \in User, \E m \in Message: send(c,u,m)
    \/ \E u \in User: \E m \in inbox[c][u]: read(c,u,m)
    \/ \E u \in User: \E m \in inbox[c][u]: deleteFromInbox(c,u,m)
    \/ \E u \in User: \E m \in outbox[c][u]: deleteFromOutbox(c,u,m)
    \/ stutter(c)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<action, time, inbox, outbox, reads>>

Invariant == \A c \in Messaging:
    \* Read messages must be in the inbox
    /\ \A u \in User: reads[c][u] \subseteq inbox[c][u]
    \* Messages in the inbox must be addressed to the user
    /\ \A u \in User, m \in Message: m \in inbox[c][u] => m.to = u
    \* Messages in the outbox must be sent by the user
    /\ \A u \in User, m \in Message: m \in outbox[c][u] => m.from = u

=============================