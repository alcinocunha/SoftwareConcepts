module Apps/FileSharing2
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

// Shared files must be uploaded
// Accessible tokens were not accessed before nor the respective file has been deleted
check Invariant {
	always {
		no Reaction iff {
			shared.Token in uploaded
			all f : File, t : Token | t in f.shared implies before ((no u : User | P.access[u,t]) since (some u : User | P.share[u,f,t]))
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Additional (redundant) properties

// Tokens can only accessed once
check SingleAccess {
	all t : Token | always {
		(some u : User | P.access[u,t]) implies after always (no u : User | P.access[u,t])
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Scenarios

// One user shares a file, then deletes it, then empties the trash, then a reaction will revoke the token
run Scenario1 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; T.delete[User,f]; T.empty[User]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 2 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; T.delete[User,f]; T.restore[User,f]; P.access[User,t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 2 Reaction expect 1

// One user shares a file, then tries to revoke the token
run Scenario3 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; P.revoke[User,f,t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 2 Reaction expect 0

// Reactions

/*
reaction EmptyRevoke[t]
when
	T.empty[u]
where
	f in trashed and t in f.shared
then
	some u : User | P.revoke[u,f,t]
*/

var lone sig EmptyRevoke extends Reaction { var t : Token }
pred EmptyRevoke[ x : Token ] { some r : EmptyRevoke | r.t = x }

fact {
	all t : Token | always {
		EmptyRevoke[t] iff {
			some u : User, f : File | before {
				not (some u : User | P.revoke[u,f,t]) since (T.empty[u] and f in trashed and t in f.shared)
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
	f in uploaded
*/

fact {
	all u : User, f : File, t : Token | always {
		P.share[u,f,t] implies f in uploaded
	}
}

/*
when
	P.access[u,t]
require
	not (AccessRevoke[t] or EmptyRevoke[t])
*/

fact {
	all u : User, t : Token | always {
		P.access[u,t] implies not (AccessRevoke[t] or EmptyRevoke[t])
	}
}

/*
when
	T.create[u,f]
require
	no f.shared
*/

fact {
	all u : User, f : File | always {
		T.create[u,f] implies no f.shared
	}
}

// Additional preventions

/*
when
	P.access[u,t]
require
	shared.t in uploaded - trashed
*/

fact {
	all u : User, t : Token | always {
		P.access[u,t] implies shared.t not in trashed
	}
}

/*
when
	P.share[u,f,t]
require
	f not in trashed
*/

fact {
	all u : User, f : File, t : Token | always {
		P.share[u,f,t] implies f not in trashed
	}
}

/*
when
	P.revoke[u,f,t]
require
	AccessRevoke[t] or DeleteRevoke[t]
*/

fact {
	all u : User, f : File, t : Token | always {
		P.revoke[u,f,t] implies (AccessRevoke[t] or EmptyRevoke[t])
	}
}
