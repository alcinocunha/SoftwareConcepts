module Apps/WPR/FileSharing2
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
fun downloaded : set Token { P.accessed }

// App specific action names

pred upload[f : File] { T.create[f] }
pred delete[f : File] { T.delete[f] }
pred restore[f : File] { T.restore[f] }
pred empty { T.empty }
pred share[f : File, t : Token] { P.share[f,t] }
pred download[t : Token] { P.access[t] }

// This app assumes reactions have priority over requests

fact {
	PriorityToReactions
}

// The design goal

// The shared tokes are those that have been shared while the respective file was accessible
// and not deleted nor downloaded afterwards
// The downloaded tokens are those that have been accessed when the respective file was accessible
check Design {
	always {
		no reactions iff {
			shared = { f : File, t : Token | before (not (f in trashed and empty[] or download[t]) since (share[f,t] and f in uploaded)) }
			downloaded = { t : Token | before once (download[t] and shared.t not in trashed) }
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Additional properties

// Some invariants
check Invariants {
	always {
		no reactions implies {
			shared.Token in uploaded
			accessed in revoked			
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Expected revoked value
check Revoked {
	always {
		no reactions implies {
			P.revoked = { t : Token | before once (download[t] or some f : File | t in f.shared and f in trashed and empty[]) }
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Tokens can only be accessed once
check SingleAccess {
	all t : Token | always {
			download[t] implies before historically not download[t]
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// A file is uploaded, shared, deleted, and the trash is emptied.
// Then a reaction will revoke the token
run Scenario1 {
	some f : File, t : Token {
		upload[f]; share[f,t]; delete[f]; empty[]
	}
	eventually always no reactions
} for exactly 1 File, exactly 1 Token, 10 Action, 10 Reaction expect 1

// A file is uploaded, shared, deleted, restored, and downloaded.
run Scenario2 {
	some f : File, t : Token {
		upload[f]; share[f,t]; delete[f]; restore[f]; download[t]
	}
	eventually always no reactions
} for exactly 1 File, exactly 1 Token, 10 Action, 10 Reaction expect 1

// A file is uploaded and shared.
// Then one tries to revoke the token, which should not be possible.
run Scenario3 {
	some f : File, t : Token {
		upload[f]; share[f,t]; P.revoke[t]
	}
	eventually always no reactions
} for exactly 1 File, exactly 1 Token, 10 Action, 10 Reaction expect 0

// Reactions

/*
reaction empty_revoke
when
	T.empty[]
where
	f in T.trashed and t in f.shared
then
	P.revoke[t]
*/

sig Empty_Revoke extends Reaction { token : Token }
fact { 
	all x,y : Empty_Revoke | x.token = y.token implies x = y
}
fact {
	all t : Token | always {
		(some r : Empty_Revoke & reactions_to_add | r.token = t) iff (some f : File | T.empty[] and f in T.trashed and t in f.shared)
		(some r : Empty_Revoke & reactions_to_remove | r.token = t) iff P.revoke[t]
	}
}

/*
reaction access_revoke
when
	P.access[t]
then
	P.revoke[t]
*/

sig Access_Revoke extends Reaction { token : Token }
fact {
	all x,y : Access_Revoke | x.token = y.token implies x = y
}
fact {
	all t : Token | always {
		(some r : Access_Revoke & reactions_to_add | r.token = t) iff P.access[t]
		(some r : Access_Revoke & reactions_to_remove | r.token = t) iff P.revoke[t]
	}
}	

/*
reaction share_error
when
	P.share[f,t]
where
	f not in uploaded
then
	error
*/

lone sig Share_Error extends Reaction { }
fact {
	always {
		some Share_Error & reactions_to_add iff (some f : File, t : Token | P.share[f,t] and f not in uploaded)
		some Share_Error & reactions_to_remove iff error
	}
}

/*
reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed and shared.t in uploaded
then
	error
*/

lone sig Revoke_Error extends Reaction { }
fact {
	always {
		some Revoke_Error & reactions_to_add iff (some t : Token | P.revoke[t] and t not in P.accessed and shared.t in uploaded)
		some Revoke_Error & reactions_to_remove iff error
	}
}

/*
reaction access_error
when
	P.access[t]
where
	shared.t in T.trashed
then
	error
*/

lone sig Access_Error extends Reaction { }
fact {
	always {
		some Access_Error & reactions_to_add iff (some t : Token | P.access[t] and shared.t in T.trashed)
		some Access_Error & reactions_to_remove iff error
	}	
}
