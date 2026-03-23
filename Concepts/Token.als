module Concepts/Token[User,Resource,Token]
open Action[User]

// State

one sig State {
	var tokens_ : Resource -> set Token,
	var revoked_ : set Token,
	var accessed_ : set Token
}

fun tokens : Resource -> set Token { State.tokens_ }
fun revoked : set Token { State.revoked_ }
fun accessed : set Token { State.accessed_ }

// Initial state

fact Init {
	no tokens
	no revoked
	no accessed
}

// Actions

var abstract sig TokenAction extends Action { var t : Token }

var sig Share extends TokenAction { var r : Resource } {
	t not in Resource.tokens
	tokens' = tokens + r->t
	revoked' = revoked
	accessed' = accessed
}

var sig Revoke extends TokenAction { var r : Resource } {
	t in r.tokens
	t not in revoked + accessed
	tokens' = tokens
	revoked' = revoked + t
	accessed' = accessed
}

var sig Access extends TokenAction { } {
	some tokens.t
	t not in revoked + accessed
	tokens' = tokens
	revoked' = revoked
	accessed' = accessed + t
}

fact Stutter {
	always {
		no TokenAction implies {
			tokens' = tokens
			revoked' = revoked
			accessed' = accessed
		}
	}
}

pred share [ v : User, x : Resource, y : Token ] { some Share and Share.u = v and Share.r = x and Share.t = y }
pred revoke [ v : User, x : Resource, y : Token ] { some Revoke and Revoke.u = v and Revoke.r = x and Revoke.t = y }
pred access [ v : User, y : Token ] { some Access and Access.u = v and Access.t = y }

// Properties

check Invariant {
	always {
		revoked + accessed in Resource.tokens
		no revoked & accessed
	}
} for 3 but 1 User, 3 Action

check Monotonicity {
	always {
		tokens in tokens'
		revoked in revoked'
		accessed in accessed'
	}
} for 3 but 1 User, 3 Action

check Principle1 {
	// access only possible after share
	all t : Token {
		(some r : Resource | share[User,r,t]) releases not access[User,t]
	}
} for 3 but exactly 1 User, 3 Action

check Principle2 {
	// can only access once
	all t : Token | always {
		access[User,t] implies after always not access[User,t]
	}
} for 3 but exactly 1 User, 3 Action

// Scenarios

run Scenario1 {
	some r : Resource, disj t,u : Token {
		share[User,r,t]; share[User,r,u]; access[User,t]; access[User,u]
	}
} for 3 but exactly 1 User expect 1

run Scenario2 {
	some r,s : Resource, t : Token {
		share[User,r,t]; access[User,t]; share[User,s,t]
	}
} for 3 but exactly 1 User expect 0
