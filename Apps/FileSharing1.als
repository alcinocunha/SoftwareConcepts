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

// App specific views of the state of the concepts to simplify the specification and visualization

fun uploaded : set File { T.accessible + T.trashed }
fun trashed : set File { T.trashed }
fun shared : File -> Token { P.urls :> (Token - P.revoked) }

// App specific action names

pred upload[f : File] { T.create[f] }
pred delete[f : File] { T.delete[f] }
pred restore[f : File] { T.restore[f] }
pred empty { T.empty }
pred share[f : File, t : Token] { P.share[f,t] }
pred download[t : Token] { P.access[t] }

// The design goal

// The shared tokes are those that have been shared while the respective file was accessible
// and not deleted nor downloaded afterwards
check Design {
	always {
		no reactions iff {
			shared = { f : File, t : Token | before (not (delete[f] or download[t]) since (share[f,t] and f in uploaded - trashed))}
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Additional properties

check Invariant {
	always {
		no reactions implies {
			shared.Token in uploaded - trashed
			accessed in revoked			
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Expected revoked value
check Revoked {
	always {
		no reactions implies {
			P.revoked = { t : Token | before once (download[t] or some f : File | t in f.shared and delete[f]) }
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Downloaded files must be uploaded and not trashed
check DownloadedAreAccessible {
	all t : Token | always {
		download[t] implies shared.t in uploaded - trashed
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Tokens can only be accessed once
check SingleAccess {
	all t : Token | always {
		download[t] implies before historically not download[t]
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// A file is uploaded, shared twice, accessed, and deleted. Reactions should revoke all tokens.
run Scenario1 {
	some f : File, t,u : Token {
		upload[f]; share[f,t]; share[f,u]; download[u]; some reactions; delete[f]
	}
	eventually always no reactions
} for exactly 1 File, 2 Token, 10 Action, 10 Reaction expect 1

// A file is uploaded, shared, and deleted. 
// Then, when the reactions are finished one tries to access the token, which should not be possible.
run Scenario2 {
	some f : File, t : Token {
		upload[f]; share[f,t]; delete[f]; eventually download[t]
	}
	eventually always no reactions
} for exactly 1 File, exactly 1 Token, 10 Action, 10 Reaction expect 0

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
reaction delete_revoke
when
	T.delete[f]
where
	t in f.shared
then
	P.revoke[t]
*/

sig Delete_Revoke extends Reaction { token : Token }
fact {
	all x,y : Delete_Revoke | x.token = y.token implies x = y
}

fact {
	all t : Token | always {
		(some d : Delete_Revoke & reactions_to_add | d.token = t) iff (some f : File | T.delete[f] and t in f.shared)
		(some d : Delete_Revoke & reactions_to_remove | d.token = t) iff P.revoke[t]
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
		(some d : Access_Revoke & reactions_to_add | d.token = t) iff P.access[t]
		(some d : Access_Revoke & reactions_to_remove | d.token = t) iff P.revoke[t]
	}
}

/*
reaction share_error
when
	P.share[f,t]
where
	f not in uploaded - T.trashed
then
	error
*/

sig Share_Error extends Reaction {}
fact {
	all x,y : Share_Error | x = y
}
fact {
	always {
		some Share_Error & reactions_to_add iff (some f : File, t : Token | P.share[f,t] and f not in uploaded - T.trashed)
		some Share_Error & reactions_to_remove iff error
	}
}

/*
reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed and shared.t not in T.trashed
then
	error
*/

sig Revoke_Error extends Reaction {}
fact {
	all x,y : Revoke_Error | x = y
}
fact {
	always {
		some Revoke_Error & reactions_to_add iff (some t : Token | P.revoke[t] and t not in P.accessed and shared.t not in T.trashed)
		some Revoke_Error & reactions_to_remove iff error
	}
}
