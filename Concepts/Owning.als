module Concepts/Owning[User,Thing]
open Action

// State

abstract sig Owning extends Concept {
    var owns : User -> Thing
}

// Initial state

fact Init {
    no owns
}

// Actions

abstract sig OwningAction extends Action { user : User, thing : Thing } { concept in Owning }
sig Acquire extends OwningAction {}
fact {
    all x,y : Acquire | x.concept = y.concept and x.user = y.user and x.thing = y.thing implies x = y
}
sig Release extends OwningAction {}
fact {    
    all x,y : Release | x.concept = y.concept and x.user = y.user and x.thing = y.thing implies x = y 
}

pred acquire [c : Owning, u : User, t : Thing] {
    no c.owns.t
    owns' = owns + c->u->t

    some a : Acquire | a.concept = c and a.user = u and a.thing = t and occurred' = a
}

pred release [c : Owning, u : User, t : Thing] {
     c.owns.t = u
     owns' = owns - c->u->t

    some a : Release | a.concept = c and a.user = u and a.thing = t and occurred' = a
}

pred stutter {
    owns' = owns

    no occurred' & OwningAction
}

fact Actions {
    always {
        (some c : Owning, u : User, t : Thing | acquire[c,u,t]) or
        (some c : Owning, u : User, t : Thing | release[c,u,t])
    }
}

// Properties

// A thing can only be owned by one user at a time
check Invariant {
    always {
        all t : Thing | lone owns.t
    }
} for 3 but 10 Action, exactly 1 Owning expect 0

// After a thing is acquired it can only be acquired again after it is released
check Principle {
	all t : Thing, u,v : User | always {
		Owning.acquire[u,t] implies after (Owning.release[u,t] releases not Owning.acquire[v,t])
	}
} for 3 but 10 Action, exactly 1 Owning

// Scenarios

run Scenario {
	eventually {
        Owning.owns = User->Thing
		eventually no owns
	}
} for exactly 1 User, exactly 3 Thing, 10 Action, exactly 1 Owning expect 1
