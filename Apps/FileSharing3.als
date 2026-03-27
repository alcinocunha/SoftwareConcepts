module Apps/FileSharing3
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
			shared.Token = uploaded - trashed
			no File & trashed
			all f : File, t : Token | t in f.shared implies before ((no u : User | P.access[u,t]) since (some u : User | P.share[u,f,t]))
		}
	}
} for 2 but 7 Action, 6 Reaction expect 0

// Additional (redundant) properties

// Tokens can only accessed once
check SingleAccess {
	all t : Token | always {
		(some u : User | P.access[u,t]) implies after always (no u : User | P.access[u,t])
	}
} for 2 but 7 Action, 6 Reaction expect 0

// Scenarios

// One user creates a file, which will be automatically shared. Then accesses the token and the file will be deleted and the trash emptied.
run Scenario1 {
	some f : File, t : Token {
		T.create[User,f]
		eventually (t in f.shared and P.access[User,t])
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 4 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token {
		T.create[User,f]; P.share[User,f,t]; T.delete[User,f]
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
reaction CreateShare[f : File]
when
	T.create[u,f]
then
	some u : User, t : Token | P.share[u,f,t]
*/

var lone sig CreateShare extends Reaction { var f : File }
pred CreateShare[x : File] { some r : CreateShare | r.f = x }

fact {
	all f : File | always {
		CreateShare[f] iff {
			some u : User | before (not (some u : User, t : Token | P.share[u,f,t]) since T.create[u,f])
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

/*
reaction AccessDelete[f : File]
when
	P.access[u,t]
where
	t in f.shared
then
	some u : User | T.delete[u,f]
*/
	
var lone sig AccessDelete extends Reaction { var f : File }
pred AccessDelete [ x : File ] { some r : AccessDelete | r.f = x }

fact {
	all f : File | always {
		AccessDelete[f] iff {
			some u : User, t : Token | before {
				not (some u : User | T.delete[u,f]) since (P.access[u,t] and t in f.shared)
			}
		}
	}
}

/*
reaction AccessEmpty[f : File]
when
	P.access[u,t]
where
	t in f.shared
then
	some u : User | T.empty[u]
*/
	
var lone sig AccessEmpty extends Reaction { var f : File }
pred AccessEmpty [ x : File ] { some r : AccessEmpty | r.f = x }

fact {
	all f : File | always {
		AccessEmpty[f] iff {
			some u : User, t : Token | before {
				not (some u : User | T.empty[u]) since (P.access[u,t] and t in f.shared)
			}
		}
	}
}

// Preventions needed to ensure the invariant

/*
when
	P.share[u,f,t]
require
	CreateShare[f]
*/

fact {
	all u : User, f : File, t : Token | always {
		P.share[u,f,t] implies CreateShare[f]
	}
}

/*
when
	T.delete[u,f]
require
	AccessDelete[f]
*/

fact {
	all u : User, f : File | always {
		T.delete[u,f] implies AccessDelete[f]
	}
}

/*
when
	P.revoke[u,f,t]
require
	AccessRevoke[t]
*/

fact {
	all u : User, f : File, t : Token | always {
		P.revoke[u,f,t] implies AccessRevoke[t]
	}
}

/*
when
	P.access[u,t]
require
	not AccessRevoke[t]
*/

fact {
	all u : User, t : Token | always {
		P.access[u,t] implies not AccessRevoke[t]
	}
}

/*
when
	T.restore[u,f]
require
	false
*/

fact {
	all u : User, f : File | always {
		T.restore[u,f] implies false
	}
}

// Additional preventions
