-------- MODULE Chat --------

EXTENDS Naturals, TLC

CONSTANTS Chat, User, Content, MaxTime, None

ASSUME 
    /\ MaxTime \in Nat
    /\ None \notin Nat

Time == 0..MaxTime

Symmetry == Permutations(User) \cup Permutations(Content)

VARIABLES action, time, sent, joined, reads

Message == [ from: User, content: Content, when : Time ]

TypeOK ==
    /\ time \in Time
    /\ sent \in [ Chat -> SUBSET Message ]
    /\ joined \in [ Chat -> [User -> Time \cup {None} ] ]
    /\ reads \in [ Chat -> [ User -> SUBSET Message ] ]

Actions == Chat \X {"join", "leave"} \X User \cup Chat \X {"send","delete","read"} \X User \X Message

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ time = 0
    /\ sent = [ c \in Chat |-> {} ]
    /\ joined = [ c \in Chat |-> [ u \in User |-> None ] ]
    /\ reads = [ c \in Chat |-> [ u \in User |-> {} ] ]

join(c,u) ==
    /\ action = <<c, "join", u>>
    /\ joined[c][u] = None
    /\ joined' = [ joined EXCEPT ![c][u] = time ]
    /\ UNCHANGED <<sent, reads, time>>

leave(c,u) ==
    /\ action = <<c, "leave", u>>
    /\ joined[c][u] # None
    /\ joined' = [ joined EXCEPT ![c][u] = None ]
    /\ reads' = [ reads EXCEPT ![c][u] = {} ]
    /\ UNCHANGED <<sent, time>>

send(c,u,x) == 
    /\ action = <<c, "send", u, x>>
    /\ time < MaxTime
    /\ joined[c][u] # None
    /\ sent' = [ sent EXCEPT ![c] = @ \cup { [from |-> u, content |-> x, when |-> time] } ]
    /\ reads' = [ reads EXCEPT ![c][u] = @ \cup { [from |-> u, content |-> x, when |-> time] } ]
    /\ time' = time + 1
    /\ UNCHANGED joined

delete(c,u,m) ==
    /\ action = <<c, "delete", u, m>>
    /\ joined[c][u] # None
    /\ m \in sent[c]
    /\ m.from = u
    /\ sent' = [ sent EXCEPT ![c] = @ \ {m} ]
    /\ reads' = [ reads EXCEPT ![c] = [ v \in User |-> reads[c][v] \ {m} ] ]
    /\ UNCHANGED <<joined, time>>

read(c,u,m) ==
    /\ action = <<c, "read", u, m>>
    /\ joined[c][u] # None
    /\ m \in sent[c]
    /\ m \notin reads[c][u]
    /\ m.when >= CHOOSE t \in joined[c][u] : TRUE
    /\ reads' = [ reads EXCEPT ![c][u] = @ \cup {m} ]
    /\ UNCHANGED <<joined, sent, time>>

stutter(c) ==
    /\ action[1] # c
    /\ UNCHANGED <<time, sent, joined, reads>>

Next == \E c \in Chat:
    \/ \E u \in User: join(c,u)
    \/ \E u \in User: leave(c,u)
    \/ \E u \in User, x \in Content: send(c,u,x)
    \/ \E u \in User, m \in Message: delete(c,u,m)
    \/ \E u \in User, m \in Message: read(c,u,m)
    \/ stutter(c)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<action, time, sent, joined, reads>>

Invariant == \A c \in Chat:
    \* Read messages must be in the chat
    /\ \A u \in User: reads[c][u] \subseteq sent[c]
    \* Users cannot read messages sent before they joined
    /\ \A u \in User, m \in Message: m \in reads[c][u] => \E t \in joined[c][u]: m.when >= t
    \* At most one message was sent at a time
    /\ \A m1, m2 \in Message : m1 \in sent[c] /\ m2 \in sent[c] /\ m1.when = m2.when => m1 = m2
    \* All sent messages have a time stamp that is strictly anterior to the current time
    /\ \A m \in Message: m \in sent[c] => m.when < time
    \* All joining time stamps are anterior to the current time
    /\ \A u \in User: joined[c][u] # None => joined[c][u] <= time

=============================