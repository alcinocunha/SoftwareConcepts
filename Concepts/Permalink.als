module Concepts/Permalink[Resource,URL]
open Action

// State

abstract sig Permalink extends Concept {
	var urls : Resource -> set URL,
	var revoked : set URL,
	var accessed : set URL
}

// Initial state

fact Init {
	no urls
	no revoked
	no accessed
}

// Actions

abstract sig PermalinkAction extends Action { label : URL } { concept in Permalink }

sig Share extends PermalinkAction { resource : Resource }
fact {
	all x,y : Share | x.concept = y.concept and x.resource = y.resource and x.label = y.label implies x = y
}
sig Revoke extends PermalinkAction {}
fact {
	all x,y : Revoke | x.concept = y.concept and x.label = y.label implies x = y
}
sig Access extends PermalinkAction {}
fact {	all x,y : Access | x.concept = y.concept and x.label = y.label implies x = y }

pred share [c : Permalink, r : Resource, l : URL] {
	l not in c.urls[Resource]
	urls' = urls + c->r->l
	revoked' = revoked
	accessed' = accessed

	some a : Share | a.concept = c and a.resource = r and a.label = l and occurred' = a
}

pred revoke [c : Permalink, l : URL] {
	l in c.urls[Resource]
	l not in c.revoked
	urls' = urls
	revoked' = revoked + c->l
	accessed' = accessed

	some a : Revoke | a.concept = c and a.label = l and occurred' = a
}

pred access [c : Permalink, l : URL] {
	some c.urls.l
	l not in c.revoked
	urls' = urls
	revoked' = revoked
	accessed' = accessed + c->l

	some a : Access | a.concept = c and a.label = l and occurred' = a
}

pred stutter {
	urls' = urls
	revoked' = revoked
	accessed' = accessed

	no occurred' & PermalinkAction
}

fact Actions {
	always {
		(some c : Permalink, r : Resource, l : URL | share[c,r,l]) or 
		(some c : Permalink, l : URL | revoke[c,l]) or 
		(some c : Permalink, l : URL | access[c,l]) or 
		stutter
	}
}

// Properties

// Revoked and accessed urls are associated with some resource
check Invariant {
	always {
		Permalink.(revoked + accessed) in Permalink.urls[Resource]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Expected value of urls
check Urls {
	all r : Resource, u : URL | always {
		r->u in Permalink.urls iff before {
			once Permalink.share[r,u]
		}
	} 
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Expected value of revoked
check Revoked {
	all u : URL | always {
		u in Permalink.revoked iff before {
			once Permalink.revoke[u]
		}
	} 
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Expected value of accessed
check Accessed {
	all u : URL | always {
		u in Permalink.accessed iff before {
			once Permalink.access[u]
		}
	} 
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Nothing is ever deleted from the state variables
check Monotonicity {
	always {
		urls in urls'
		revoked in revoked'
		accessed in accessed'
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Access only possible after share
check Principle1 {
	all l : URL {
		(some r : Resource | Permalink.share[r,l]) releases not Permalink.access[l]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Can only share token once
check Principle2 {
	all l : URL | always {
		(some r : Resource | Permalink.share[r,l]) implies after always (no r : Resource | Permalink.share[r,l])
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0

// Scenarios

run Scenario1 {
	some r : Resource, disj l,m : URL {
		Permalink.share[r,l]; Permalink.share[r,m]; Permalink.access[l]; Permalink.revoke[l];Permalink.access[m]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 1

run Scenario2 {
	some r : Resource, l : URL {
		Permalink.share[r,l]; Permalink.access[l]; Permalink.access[l]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 1

run Scenario3 {
	some r : Resource, disj l,m : URL {
		Permalink.share[r,l]; Permalink.access[l]; Permalink.access[m]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0

run Scenario4 {
	some r,s : Resource, l : URL {
		Permalink.share[r,l]; Permalink.share[s,l]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0

run Scenario5 {
	some r : Resource, l : URL {
		Permalink.share[r,l]; Permalink.revoke[l]; Permalink.access[l]
	}
} for 3 but 10 Action, exactly 1 Permalink expect 0
