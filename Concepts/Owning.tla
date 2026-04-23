-------- MODULE Owning --------

CONSTANTS Owning, User, Resource

VARIABLES action, owns

TypeOK ==
    owns \in [ Owning -> [ User -> SUBSET Resource ] ]

Actions == Owning \X {"acquire", "release"} \X User \X Resource

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    owns = [ o \in Owning |-> [ u \in User |-> {} ] ]

acquire(o,u,r) ==
    /\ action = <<o, "acquire", u, r>>
    /\ \A v \in User: r \notin owns[o][v]
    /\ owns' = [ owns EXCEPT ![o][u] = @ \cup {r} ]

release(o,u,r) ==
    /\ action = <<o, "release", u, r>>
    /\ r \in owns[o][u]
    /\ owns' = [ owns EXCEPT ![o][u] = @ \ {r} ]

stutter(o) ==
    /\ action[1] # o
    /\ UNCHANGED owns

Next == \E o \in Owning:
    \/ \E u \in User, r \in Resource: acquire(o,u,r)
    \/ \E u \in User, r \in Resource: release(o,u,r)
    \/ stutter(o)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<action, owns>>

Invariant ==
    \A o \in Owning, r \in Resource: \A u, v \in User: r \in owns[o][u] /\ r \in owns[o][v] => u = v

===============================