module Apps/FileSharing1
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
			all f : File, t : Token | t in f.shared implies before (not (T.delete[f] or P.access[t]) since P.share[f,t])
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Additional redundant properties

// Accessed files must be uploaded and not trashed
check AccessedAreAccessible {
	all t : Token | always {
		P.access[t] implies shared.t in uploaded - trashed
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Tokens can only accessed once
check SingleAccess {
	all t : Token | always {
		P.access[t] implies after always not P.access[t]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Scenarios

// One user shares a file, then deletes it, then a reaction will revoke the token
run Scenario1 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; T.delete[f]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; T.delete[f]; T.restore[f]; P.access[t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 0

// One user shares a file, then tries to revoke the token
run Scenario3 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; P.revoke[f,t]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 0

// Reactions

/*
reaction DeleteRevoke[t : Token]
when
	T.delete[f]
where
	t in f.shared
then
	P.revoke[f,t]
*/

var lone sig DeleteRevoke extends Reaction { var t : Token }
pred DeleteRevoke [ x : Token ] { some r : DeleteRevoke | r.t = x }

fact {
	all t : Token | always {
		DeleteRevoke[t] iff {
			some f : File | before {
				not P.revoke[f,t] since (T.delete[f] and t in f.shared)
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
	f in uploaded - trashed
*/

fact {
	all f : File, t : Token | always {
		P.share[f,t] implies f in uploaded - trashed
	}
}

/*
when
	P.access[t]
require
	not (AccessRevoke[t] or DeleteRevoke[t])
*/

fact {
	all t : Token | always {
		P.access[t] implies not (AccessRevoke[t] or DeleteRevoke[t])
	}
}

// Additional preventions

/*
when
	P.revoke[f,t]
require
	AccessRevoke[t] or DeleteRevoke[t]
*/

fact {
	all f : File, t : Token | always {
		P.revoke[f,t] implies (AccessRevoke[t] or DeleteRevoke[t])
	}
}
