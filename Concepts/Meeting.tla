------- MODULE Meeting -------

CONSTANTS Meeting, User

VARIABLES action, host, participants

TypeOK ==
    /\ host \in [ Meeting -> SUBSET User ]
    /\ participants \in [ Meeting -> SUBSET User ]

Actions == Meeting \X {"start", "end", "join", "leave"} \X User

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ host = [ m \in Meeting |-> {} ]
    /\ participants = [ m \in Meeting |-> {} ]

start(m,u) ==
    /\ action = <<m, "start", u>>
    /\ host[m] = {}
    /\ host' = [ host EXCEPT ![m] = {u} ]
    /\ UNCHANGED participants

end(m,u) ==
    /\ action = <<m, "end", u>>
    /\ host[m] = {u}
    /\ host' = [ host EXCEPT ![m] = {} ]
    /\ participants' = [ participants EXCEPT ![m] = {} ]

join(m,u) ==
    /\ action = <<m, "join", u>>
    /\ host[m] # {}
    /\ u \notin participants[m]
    /\ participants' = [ participants EXCEPT ![m] = @ \cup {u} ]
    /\ UNCHANGED host

leave(m,u) ==
    /\ action = <<m, "leave", u>>
    /\ u \in participants[m]
    /\ participants' = [ participants EXCEPT ![m] = @ \ {u} ]
    /\ UNCHANGED host

stutter(m) ==
    /\ action[1] # m
    /\ UNCHANGED <<host, participants>>

Next == \E m \in Meeting:
    \/ \E u \in User: start(m,u)
    \/ \E u \in User: end(m,u)
    \/ \E u \in User: join(m,u)
    \/ \E u \in User: leave(m,u)
    \/ stutter(m)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<action, host, participants>>

Invariant == \A m \in Meeting:
    /\ participants[m] # {} => host[m] # {}
    /\ \A x,y \in User: x \in host[m] /\ y \in host[m] => x = y

==============================