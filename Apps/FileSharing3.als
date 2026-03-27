module Apps/FileSharing3
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

// Shared files must be uploaded
// Accessible tokens were not accessed before nor the respective file has been deleted
check Invariant {
	always {
		no Reaction iff {
			shared.Token = uploaded - trashed
			no File & trashed
			all f : File, t : Token | t in f.shared implies before (not P.access[t] since P.share[f,t])
		}
	}
} for 2 but 7 Action, 6 Reaction expect 0

// Additional (redundant) properties

// Tokens can only accessed once
check SingleAccess {
	all t : Token | always {
		P.access[t] implies after always not P.access[t]
	}
} for 2 but 7 Action, 6 Reaction expect 0

// Scenarios

// One user creates a file, which will be automatically shared. Then accesses the token and the file will be deleted and the trash emptied.
run Scenario1 {
	some f : File, t : Token {
		T.create[f]
		eventually (t in f.shared and P.access[t])
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 4 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token {
		T.create[f]; P.share[f,t]; T.delete[f]
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
reaction CreateShare[f : File]
when
	T.create[f]
then
	some t : Token | P.share[f,t]
*/

var lone sig CreateShare extends Reaction { var f : File }
pred CreateShare[x : File] { some r : CreateShare | r.f = x }

fact {
	all f : File | always {
		CreateShare[f] iff {
			before (not (some t : Token | P.share[f,t]) since T.create[f])
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

/*
reaction AccessDelete[f : File]
when
	P.access[t]
where
	t in f.shared
then
	T.delete[f]
*/
	
var lone sig AccessDelete extends Reaction { var f : File }
pred AccessDelete [ x : File ] { some r : AccessDelete | r.f = x }

fact {
	all f : File | always {
		AccessDelete[f] iff {
			some t : Token | before {
				not T.delete[f] since (P.access[t] and t in f.shared)
			}
		}
	}
}

/*
reaction AccessEmpty[f : File]
when
	P.access[t]
where
	t in f.shared
then
	T.empty[]
*/
	
var lone sig AccessEmpty extends Reaction { var f : File }
pred AccessEmpty [ x : File ] { some r : AccessEmpty | r.f = x }

fact {
	all f : File | always {
		AccessEmpty[f] iff {
			some t : Token | before {
				not T.empty[] since (P.access[t] and t in f.shared)
			}
		}
	}
}

// Preventions needed to ensure the invariant

/*
when
	P.share[f,t]
require
	CreateShare[f]
*/

fact {
	all f : File, t : Token | always {
		P.share[f,t] implies CreateShare[f]
	}
}

/*
when
	T.delete[f]
require
	AccessDelete[f]
*/

fact {
	all f : File | always {
		T.delete[f] implies AccessDelete[f]
	}
}

/*
when
	P.revoke[f,t]
require
	AccessRevoke[t]
*/

fact {
	all f : File, t : Token | always {
		P.revoke[f,t] implies AccessRevoke[t]
	}
}

/*
when
	P.access[t]
require
	not AccessRevoke[t]
*/

fact {
	all t : Token | always {
		P.access[t] implies not AccessRevoke[t]
	}
}

/*
when
	T.restore[f]
require
	false
*/

fact {
	all f : File | always {
		T.restore[f] implies false
	}
}

// Additional preventions
