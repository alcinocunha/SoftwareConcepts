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

var abstract sig PermalinkAction extends Action { var l : URL } { c in Permalink }

var sig Share extends PermalinkAction { var r : Resource } {
	l not in c.urls[Resource]
	urls' = urls + c->r->l
	revoked' = revoked
	accessed' = accessed
}

var sig Revoke extends PermalinkAction { } {
	l in c.urls[Resource]
	l not in c.revoked
	urls' = urls
	revoked' = revoked + c->l
	accessed' = accessed
}

var sig Access extends PermalinkAction { } {
	some c.urls.l
	l not in c.revoked
	urls' = urls
	revoked' = revoked
	accessed' = accessed + c->l
}

fact Stutter {
	always {
		no PermalinkAction implies {
			urls' = urls
			revoked' = revoked
			accessed' = accessed
		}
	}
}

pred share [ p : Permalink, x : Resource, y : URL ] { some Share and Share.c = p and Share.r = x and Share.l = y }
pred revoke [ p : Permalink, y : URL ] { some Revoke and Revoke.c = p and Revoke.l = y }
pred access [ p : Permalink, y : URL ] { some Access and Access.c = p and Access.l = y }

// Properties

// Revoked and accessed urls are associated with some resource
check Invariant {
	always {
		Permalink.(revoked + accessed) in Permalink.urls[Resource]
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Expected value of urls
check Urls {
	all r : Resource, u : URL | always {
		r->u in Permalink.urls iff before {
			once Permalink.share[r,u]
		}
	} 
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Expected value of revoked
check Revoked {
	all u : URL | always {
		u in Permalink.revoked iff before {
			once Permalink.revoke[u]
		}
	} 
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Expected value of accessed
check Accessed {
	all u : URL | always {
		u in Permalink.accessed iff before {
			once Permalink.access[u]
		}
	} 
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Nothing is ever deleted from the state variables
check Monotonicity {
	always {
		urls in urls'
		revoked in revoked'
		accessed in accessed'
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Access only possible after share
check Principle1 {
	all l : URL {
		(some r : Resource | Permalink.share[r,l]) releases not Permalink.access[l]
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Can only share token once
check Principle2 {
	all l : URL | always {
		(some r : Resource | Permalink.share[r,l]) implies after always (no r : Resource | Permalink.share[r,l])
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Scenarios

run Scenario1 {
	some r : Resource, disj l,m : URL {
		Permalink.share[r,l]; Permalink.share[r,m]; Permalink.access[l]; Permalink.revoke[l];Permalink.access[m]
	}
} for 3 but  exactly 1 Permalink expect 1

run Scenario2 {
	some r : Resource, l : URL {
		Permalink.share[r,l]; Permalink.access[l]; Permalink.access[l]
	}
} for 3 but exactly 1 Permalink expect 1

run Scenario3 {
	some r : Resource, disj l,m : URL {
		Permalink.share[r,l]; Permalink.access[l]; Permalink.access[m]
	}
} for 3 but exactly 1 Permalink expect 0

run Scenario4 {
	some r,s : Resource, l : URL {
		Permalink.share[r,l]; Permalink.share[s,l]
	}
} for 3 but exactly 1 Permalink expect 0

run Scenario5 {
	some r : Resource, l : URL {
		Permalink.share[r,l]; Permalink.revoke[l]; Permalink.access[l]
	}
} for 3 but exactly 1 Permalink expect 0
