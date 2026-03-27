module Apps/FileSharing1
open Action
open Reaction

// Composed concepts

open Concepts/Trash[File]
open Concepts/Permalink[File,Token]

// All users share the same trash and token concepts

one sig T extends Trash {}
one sig P extends Permalink {}

// Types

sig File {}
sig Token {}

// App specific relations

fun uploaded : set File { T.accessible + T.trashed }
fun trashed : set File { T.trashed }
fun shared : File -> Token { P.urls :> (Token - P.revoked) }

// The app invariant

// Shared files must be accessible
// Accessible tokens were not accessed before nor the respective file has been deleted
check Invariant {
	always {
		no Reaction iff {
			shared.Token in uploaded - trashed
			all f : File, t : Token | t in f.shared implies before ((no u : User | T.delete[u,f] or P.access[u,t]) since (some u : User | P.share[u,f,t]))
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Additional redundant properties

// Accessed files must be uploaded and not trashed
check AccessedAreAccessible {
	all t : Token | always {
		(some u : User | P.access[u,t]) implies shared.t in uploaded - trashed
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Tokens can only accessed once
check SingleAccess {
	all t : Token | always {
		(some u : User | P.access[u,t]) implies after always (no u : User | P.access[u,t])
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Scenarios

// One user shares a file, then deletes it, then a reaction will revoke the token
run Scenario1 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; T.delete[User,f]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 2 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; T.delete[User,f]; T.restore[User,f]; P.access[User,t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 2 Reaction expect 0

// One user shares a file, then tries to revoke the token
run Scenario3 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; P.revoke[User,f,t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 2 Reaction expect 0

// Reactions

/*
reaction DeleteRevoke[t : Token]
when
	T.delete[u,f]
where
	t in f.shared
then
	some u : User | P.revoke[u,f,t]
*/

var lone sig DeleteRevoke extends Reaction { var t : Token }
pred DeleteRevoke [ x : Token ] { some r : DeleteRevoke | r.t = x }

fact {
	all t : Token | always {
		DeleteRevoke[t] iff {
			some u : User, f : File | before {
				not (some u : User | P.revoke[u,f,t]) since (T.delete[u,f] and t in f.shared)
			}
		}
	}
}

/*
reaction AccessRevoke[t : Token]
when
	P.access[u,t]
where
	t in f.shared
then
	some u : User | P.revoke[u,f,t]
*/

var lone sig AccessRevoke extends Reaction { var t : Token }
pred AccessRevoke [ x : Token ] { some r : AccessRevoke | r.t = x }

fact {
	all t : Token | always {
		AccessRevoke[t] iff {
			some u : User, f : File | before {
				not (some u : User | P.revoke[u,f,t]) since (P.access[u,t] and t in f.shared)
			}
		}
	}
}

// Preventions needed to ensure the app invariant

/*
when
	P.share[u,f,t]
require
	f in uploaded - trashed
*/

fact {
	all u : User, f : File, t : Token | always {
		P.share[u,f,t] implies f in uploaded - trashed
	}
}

/*
when
	P.access[u,t]
require
	not (AccessRevoke[t] or DeleteRevoke[t])
*/

fact {
	all u : User, t : Token | always {
		P.access[u,t] implies not (AccessRevoke[t] or DeleteRevoke[t])
	}
}

// Additional preventions

/*
when
	P.revoke[u,f,t]
require
	AccessRevoke[t] or DeleteRevoke[t]
*/

fact {
	all u : User, f : File, t : Token | always {
		P.revoke[u,f,t] implies (AccessRevoke[t] or DeleteRevoke[t])
	}
}
