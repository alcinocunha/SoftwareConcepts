module Apps/FileSharing2
open Action
open Reaction

// Composed concepts

open Concepts/Trash[File]
open Concepts/Permalink[File,Token]

one sig T extends Trash {}
one sig P extends Permalink {}

// Types

sig File {}
sig Token {}

// App specific views of the state of the concepts to simplify the specification and visualization

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
			all f : File, t : Token | t in f.shared implies before (not P.access[t] since P.share[f,t])
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Additional (redundant) properties

// Tokens can only accessed once
check SingleAccess {
	all t : Token | always {
		P.access[t] implies after always not P.access[t]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Scenarios

// One user shares a file, then deletes it, then empties the trash, then a reaction will revoke the token
run Scenario1 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; T.delete[f]; T.empty[]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; T.delete[f]; T.restore[f]; P.access[t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 1

// One user shares a file, then tries to revoke the token
run Scenario3 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; P.revoke[f,t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 0

// Reactions

/*
reaction EmptyRevoke[t]
when
	T.empty[]
where
	f in trashed and t in f.shared
then
	P.revoke[f,t]
*/

var lone sig EmptyRevoke extends Reaction { var t : Token }
pred EmptyRevoke[ x : Token ] { some r : EmptyRevoke | r.t = x }

fact {
	all t : Token | always {
		EmptyRevoke[t] iff {
			some f : File | before {
				not P.revoke[f,t] since (T.empty[] and f in trashed and t in f.shared)
			}
		}
	}
}

/*
reaction AccessRevoke[t : Token]
when
	P.access[t]
where
	t in f.shared
then
	P.revoke[f,t]
*/

var lone sig AccessRevoke extends Reaction { var t : Token }
pred AccessRevoke [ x : Token ] { some r : AccessRevoke | r.t = x }

fact {
	all t : Token | always {
		AccessRevoke[t] iff {
			some f : File | before {
				not P.revoke[f,t] since (P.access[t] and t in f.shared)
			}
		}
	}
}

// Preventions needed to ensure the app invariant

/*
when
	P.share[f,t]
require
	f in uploaded
*/

fact {
	all f : File, t : Token | always {
		P.share[f,t] implies f in uploaded
	}
}

/*
when
	P.access[t]
require
	not (AccessRevoke[t] or EmptyRevoke[t])
*/

fact {
	all t : Token | always {
		P.access[t] implies not (AccessRevoke[t] or EmptyRevoke[t])
	}
}

/*
when
	T.create[f]
require
	no f.shared
*/

fact {
	all f : File | always {
		T.create[f] implies no f.shared
	}
}

// Additional preventions

/*
when
	P.access[t]
require
	shared.t in uploaded - trashed
*/

fact {
	all t : Token | always {
		P.access[t] implies shared.t not in trashed
	}
}

/*
when
	P.share[f,t]
require
	f not in trashed
*/

fact {
	all f : File, t : Token | always {
		P.share[f,t] implies f not in trashed
	}
}

/*
when
	P.revoke[f,t]
require
	AccessRevoke[t] or DeleteRevoke[t]
*/

fact {
	all f : File, t : Token | always {
		P.revoke[f,t] implies (AccessRevoke[t] or EmptyRevoke[t])
	}
}
