-------- MODULE Chat --------

EXTENDS Naturals, TLC

CONSTANTS Chat, User, Content, MaxTime

ASSUME MaxTime \in Nat

Time == 0..MaxTime

Symmetry == Permutations(User) \cup Permutations(Content)

VARIABLES action, time, messages, joined, reads

Message == [ from: User, content: Content, when : Time ]

TypeOK ==
    /\ time \in Time
    /\ messages \in [ Chat -> SUBSET Message ]
    /\ joined \in [ Chat -> [User -> SUBSET Time ] ]
    /\ reads \in [ Chat -> [ User -> SUBSET Message ] ]

Actions == Chat \X {"join", "leave"} \X User \cup Chat \X {"send","delete","read"} \X User \X Message

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ time = 0
    /\ messages = [ c \in Chat |-> {} ]
    /\ joined = [ c \in Chat |-> [ u \in User |-> {} ] ]
    /\ reads = [ c \in Chat |-> [ u \in User |-> {} ] ]

join(c,u) ==
    /\ action = <<c, "join", u>>
    /\ joined[c][u] = {}
    /\ joined' = [ joined EXCEPT ![c][u] = @ \cup {time} ]
    /\ UNCHANGED <<messages, reads, time>>

leave(c,u) ==
    /\ action = <<c, "leave", u>>
    /\ joined[c][u] # {}
    /\ joined' = [ joined EXCEPT ![c][u] = {} ]
    /\ reads' = [ reads EXCEPT ![c][u] = {} ]
    /\ UNCHANGED <<messages, time>>

send(c,u,m) == 
    /\ action = <<c, "send", u, m>>
    /\ time < MaxTime
    /\ joined[c][u] # {}
    /\ m.from = u
    /\ m.when = time
    /\ messages' = [ messages EXCEPT ![c] = @ \cup {m} ]
    /\ reads' = [ reads EXCEPT ![c][u] = @ \cup {m} ]
    /\ time' = time + 1
    /\ UNCHANGED joined

delete(c,u,m) ==
    /\ action = <<c, "delete", u, m>>
    /\ joined[c][u] # {}
    /\ m \in messages[c]
    /\ m.from = u
    /\ messages' = [ messages EXCEPT ![c] = @ \ {m} ]
    /\ reads' = [ reads EXCEPT ![c] = [ v \in User |-> reads[c][v] \ {m} ] ]
    /\ UNCHANGED <<joined, time>>

read(c,u,m) ==
    /\ action = <<c, "read", u, m>>
    /\ joined[c][u] # {}
    /\ m \in messages[c]
    /\ m \notin reads[c][u]
    /\ m.when >= CHOOSE t \in joined[c][u] : TRUE
    /\ reads' = [ reads EXCEPT ![c][u] = @ \cup {m} ]
    /\ UNCHANGED <<joined, messages, time>>

stutter(c) ==
    /\ action[1] # c
    /\ UNCHANGED <<time, messages, joined, reads>>

Next == \E c \in Chat:
    \/ \E u \in User: join(c,u)
    \/ \E u \in User: leave(c,u)
    \/ \E u \in User, m \in Message: send(c,u,m)
    \/ \E u \in User, m \in Message: delete(c,u,m)
    \/ \E u \in User, m \in Message: read(c,u,m)
    \/ stutter(c)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<action, time, messages, joined, reads>>

Invariant == \A c \in Chat:
    \* No double joins
    /\ \A u \in User, t1, t2 \in Time: t1 \in joined[c][u] /\ t2 \in joined[c][u] => t1 = t2
    \* Read messages must be in the chat
    /\ \A u \in User: reads[c][u] \subseteq messages[c]
    \* Users cannot read messages sent before they joined
    /\ \A u \in User, m \in Message: m \in reads[c][u] => \E t \in joined[c][u]: m.when >= t
    \* At most one message was sent at a time
    /\ \A m1, m2 \in Message : m1 \in messages[c] /\ m2 \in messages[c] /\ m1.when = m2.when => m1 = m2

=============================