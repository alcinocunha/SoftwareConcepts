------------ MODULE Reservation -------------

CONSTANTS Reservation, User, Resource

VARIABLES action, available, reservations

TypeOK ==
    /\ available \in [ Reservation -> SUBSET Resource ]
    /\ reservations \in [ Reservation -> [ User -> SUBSET Resource ] ]

Actions == Reservation \X {"reserve", "cancel", "use"} \X User \X Resource \cup Reservation \X {"provide", "retract"} \X Resource

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ available = [ r \in Reservation |-> {} ]
    /\ reservations = [ r \in Reservation |-> [ u \in User |-> {} ] ]

provide(c,r) ==
    /\ action = <<c, "provide", r>>
    /\ r \notin available[c]
    /\ available' = [ available EXCEPT ![c] = @ \cup {r} ]
    /\ reservations' = [ reservations EXCEPT ![c] = [ u \in User |-> reservations[c][u] \ {r} ] ]

retract(c,r) ==
    /\ action = <<c, "retract", r>>
    /\ r \in available[c]
    /\ \A u \in User: r \notin reservations[c][u]
    /\ available' = [ available EXCEPT ![c] = @ \ {r} ]
    /\ UNCHANGED reservations

reserve(c,u,r) ==
    /\ action = <<c, "reserve", u, r>>
    /\ r \in available[c]
    /\ \A v \in User: r \notin reservations[c][v]
    /\ reservations' = [ reservations EXCEPT ![c][u] = @ \cup {r} ]
    /\ UNCHANGED available

cancel(c,u,r) ==
    /\ action = <<c, "cancel", u, r>>
    /\ r \in available[c]
    /\ r \in reservations[c][u]
    /\ reservations' = [ reservations EXCEPT ![c][u] = @ \ {r} ]
    /\ UNCHANGED available

use(c,u,r) ==
    /\ action = <<c, "use", u, r>>
    /\ r \in available[c]
    /\ r \in reservations[c][u]
    /\ available' = [ available EXCEPT ![c] = @ \ {r} ]
    /\ UNCHANGED reservations

stutter(c) ==
    /\ action[1] # c
    /\ UNCHANGED <<available, reservations>>

Next == \E c \in Reservation:
    \/ \E r \in Resource: provide(c,r)
    \/ \E r \in Resource: retract(c,r)
    \/ \E u \in User, r \in Resource: reserve(c,u,r)
    \/ \E u \in User, r \in Resource: cancel(c,u,r)
    \/ \E u \in User, r \in Resource: use(c,u,r)
    \/ stutter(c)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<available, reservations, action>>

Invariant ==
    /\ \A c \in Reservation, r \in Resource, u,v \in User: r \in reservations[c][u] /\ r \in reservations[c][v] => u = v

=============================================