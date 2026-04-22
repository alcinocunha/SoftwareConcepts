-------------- MODULE Permalink --------------

CONSTANT Permalink, Resource, URL

VARIABLES action, urls, revoked, accessed

Actions == Permalink \X {"share"} \X Resource \X URL \cup Permalink \X {"revoke", "access"} \X URL

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ revoked = [ p \in Permalink |-> {} ]
    /\ accessed = [ p \in Permalink |-> {} ]
    /\ urls = [ p \in Permalink |-> [ r \in Resource |-> {}] ]

share(p,r,u) ==
    /\ action = <<p, "share", r, u>>
    /\ \A s \in Resource: u \notin urls[p][s]
    /\ urls' = [ urls EXCEPT ![p][r] = @ \cup {u} ]
    /\ UNCHANGED <<revoked, accessed>>

revoke(p,u) ==
    /\ action = <<p, "revoke", u>>
    /\ \E r \in Resource: u \in urls[p][r]
    /\ u \notin revoked[p]
    /\ revoked' = [ revoked EXCEPT ![p] = @ \cup {u} ]
    /\ UNCHANGED <<urls, accessed>>

access(p,u) ==
    /\ action = <<p, "access", u>>
    /\ \E r \in Resource: u \in urls[p][r]
    /\ u \notin revoked[p]
    /\ accessed' = [ accessed EXCEPT ![p] = @ \cup {u} ]
    /\ UNCHANGED <<urls, revoked>>

stutter(p) ==
    /\ action[1] # p
    /\ UNCHANGED <<urls, revoked, accessed>>

Next == \E p \in Permalink:
    \/ \E r \in Resource, u \in URL: share(p,r,u)
    \/ \E u \in URL: revoke(p,u)
    \/ \E u \in URL: access(p,u)
    \/ stutter(p)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<urls, revoked, accessed, action>>

TypeOK ==
    /\ urls \in [ Permalink -> [ Resource -> SUBSET URL ] ]
    /\ revoked \in [ Permalink -> SUBSET URL ]
    /\ accessed \in [ Permalink -> SUBSET URL ]

Invariant ==
    /\ \A p \in Permalink: revoked[p] \subseteq UNION { urls[p][r] : r \in Resource }
    /\ \A p \in Permalink: accessed[p] \subseteq UNION { urls[p][r] : r \in Resource }

==============================================