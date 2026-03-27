module Concepts/Permalink[Resource,URL]
open Action

// State

abstract sig Permalink extends Concept {
	var urls : Resource -> set URL,
	var revoked : set URL
}

// Initial state

fact Init {
	no urls
	no revoked
}

// Actions

var abstract sig PermalinkAction extends Action { var l : URL } { c in Permalink }

var sig Share extends PermalinkAction { var r : Resource } {
	l not in c.urls[Resource]
	urls' = urls + c->r->l
	revoked' = revoked
}

var sig Revoke extends PermalinkAction { var r : Resource } {
	l in c.urls[r]
	l not in c.revoked
	urls' = urls
	revoked' = revoked + c->l
}

var sig Access extends PermalinkAction { } {
	some c.urls.l
	l not in c.revoked
	urls' = urls
	revoked' = revoked
}

fact Stutter {
	always {
		no PermalinkAction implies {
			urls' = urls
			revoked' = revoked
		}
	}
}

pred share [ p : Permalink, x : Resource, y : URL ] { some Share and Share.c = p and Share.r = x and Share.l = y }
pred revoke [ p : Permalink, x : Resource, y : URL ] { some Revoke and Revoke.c = p and Revoke.r = x and Revoke.l = y }
pred access [ p : Permalink, y : URL ] { some Access and Access.c = p and Access.l = y }

// Properties

check Invariant {
	always {
		Permalink.revoked in Permalink.urls[Resource]
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

check Monotonicity {
	always {
		urls in urls'
		revoked in revoked'
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

check Principle1 {
	// access only possible after share
	all l : URL {
		(some r : Resource | Permalink.share[r,l]) releases not Permalink.access[l]
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

check Principle2 {
	// can only share token once
	all l : URL | always {
		(some r : Resource | Permalink.share[r,l]) implies after always (no r : Resource | Permalink.share[r,l])
	}
} for 3 but 3 Action, exactly 1 Permalink expect 0

// Scenarios

run Scenario1 {
	some r : Resource, disj l,m : URL {
		Permalink.share[r,l]; Permalink.share[r,m]; Permalink.access[l]; Permalink.access[m]
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
