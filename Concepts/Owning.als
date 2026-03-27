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

abstract var sig OwningAction extends Action { var u : User, var t : Thing } { c in Owning }

var sig Acquire extends OwningAction {} {
    no c.owns.t
    owns' = owns + c->u->t
}

var sig Release extends OwningAction {} {
    c.owns.t = u
    owns' = owns - c->u->t
}

fact Stutter {
    always {
        no OwningAction implies owns' = owns
    }
}

pred acquire [o : Owning, x : User, y : Thing] { some Acquire and Acquire.c = o and Acquire.u = x and Acquire.t = y }
pred release [o : Owning, x : User, y : Thing] { some Release and Release.c = o and Release.u = x and Release.t = y }

// Properties

// A thing can only be owned by one user at a time
check Invariant {
    always {
        all t : Thing | lone owns.t
    }
} for 3 but 2 Action, exactly 1 Owning expect 0

// After a thing is acquired it can only be acquired again after it is released
check Principle {
	all t : Thing, u,v : User | always {
		Owning.acquire[u,t] implies after (Owning.release[u,t] releases not Owning.acquire[v,t])
	}
} for 3 but 2 Action, exactly 1 Owning

// Scenarios

run Scenario {
	eventually {
        Owning.owns = User->Thing
		eventually no owns
	}
} for exactly 1 User, exactly 3 Thing, 2 Action, exactly 1 Owning expect 1