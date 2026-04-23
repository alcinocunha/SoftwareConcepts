module Concepts/Owning[User,Resource]
open Action

// State

abstract sig Owning extends Concept {
    var owns : User -> Resource
}

// Initial state

fact Init {
    no owns
}

// Actions

abstract sig OwningAction extends Action { user : User, resource : Resource } { concept in Owning }
sig Acquire extends OwningAction {}
fact {
    all x,y : Acquire | x.concept = y.concept and x.user = y.user and x.resource = y.resource implies x = y
}
sig Release extends OwningAction {}
fact {    
    all x,y : Release | x.concept = y.concept and x.user = y.user and x.resource = y.resource implies x = y 
}

pred acquire [c : Owning, u : User, t : Resource] {
    no c.owns.t
    c.owns' = c.owns + (u -> t)

    some a : Acquire & action | a.concept = c and a.user = u and a.resource = t
}

pred release [c : Owning, u : User, t : Resource] {
     c.owns.t = u
     c.owns' = c.owns - (u -> t)

    some a : Release & action | a.concept = c and a.user = u and a.resource = t
}

pred stutter [c : Owning] {
    c.owns' = c.owns

    no a : action | a.concept = c
}

fact Actions {
    all c : Owning | always {
        (some u : User, t : Resource | c.acquire[u,t]) or
        (some u : User, t : Resource | c.release[u,t]) or
        c.stutter[]
    }
}

// Properties

// A Resource can only be owned by one user at a time
check Invariant {
    always {
        all t : Resource | lone owns.t
    }
} for 3 but 10 Action, exactly 1 Owning expect 0

// After a Resource is acquired it can only be acquired again after it is released
check Principle {
	all t : Resource, u,v : User | always {
		Owning.acquire[u,t] implies after (Owning.release[u,t] releases not Owning.acquire[v,t])
	}
} for 3 but 10 Action, exactly 1 Owning expect 0

// Scenarios

run Scenario {
	eventually {
        Owning.owns = User->Resource
		eventually no owns
	}
} for exactly 1 User, exactly 3 Resource, 10 Action, exactly 1 Owning expect 1
