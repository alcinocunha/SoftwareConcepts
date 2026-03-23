module Apps/FileSharing1
open Action[User]
open Reaction

// Composed concepts

open Concepts/Trash[User,File]
open Concepts/Token[User,File,Token]

// Multi user app

sig User {}

// Types

sig File {}
sig Token {}
fun activeTokens [u : User, f : File] : set Token { (u.tokens[f] - revoked) - accessed }

// The app invariant

// Files with active (not revoked or accessed) tokens must be accessible
check Invariant {
	always {
		no Reaction iff {
			all u : User, f : File | some activeTokens[u,f] implies f in u.accessible
		}
	}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// One user shares a file, then deletes it, then a reaction will revoke the token
run Scenario1 {
	some f : File, t : Token | eventually {
		share[User,f,t]; delete[User,f]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 1 Reaction expect 1

// One user shares a file, then deletes it, then tries to access the token
run Scenario2 {
	some f : File, t : Token | {
		eventually (share[User,f,t]; delete[User,f])
		eventually access[User,t]
	}
} for exactly 1 File, exactly 1 Token, exactly 1 User, 7 Action, 1 Reaction expect 0

// Reactions

/*
when
	delete[u,f]
where
	t in activeTokens[u,f]
then
	revoke[u,f,t]
*/

var lone sig DeleteRevoke extends Reaction { }

fact {
	always {
		some DeleteRevoke iff {
			some u : User, f : File, t : Token | before {
				not revoke[u,f,t] since (delete[u,f] and t in activeTokens[u,f])
			}
		}
	}
}


// Preventions

/*
when
	share[u,f,t]
require
	f in u.accessible
*/

fact {
	all u : User, f : File, t : Token | always {
		share[u,f,t] implies f in u.accessible
	}
}

/*
when
	restore[u,f]
require
	no activeTokens[u,f]
*/

fact {
	all u : User, f : File | always {
		restore[u,f] implies no activeTokens[u,f]
	}
}

/*
when
	access[u,t]
require
	some accessible & tokens.t
*/

fact {
	all u : User, t : Token | always {
		access[u,t] implies some accessible & tokens.t
	}
}

/*
when
	create[u,f]
require
	no activeTokens[u,f]
*/

fact {
	all u : User, f : File | always {
		create[u,f] implies no activeTokens[u,f]
	}
}
