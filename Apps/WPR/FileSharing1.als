module FileSharing1
open Action
open Reaction

// Composed concepts

open Trash[File]
open Permalink[File,Token]

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

// Some invariants
check Invariants {
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

// Note that the following two properties are always true, unlike in the version without priority to reactions.

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

run {
	eventually some Share_Error & reactions
} for 3 but 10 Action, 10 Reaction expect 1

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
	delete[f]
where
	t in f.shared
then
	P.revoke[t]
*/

sig Delete_Revoke extends Reaction { t : Token }
fact {
	all x,y : Delete_Revoke | x.t = y.t implies x = y
	all x : Token | eventually { some f : File | delete[f] and x in f.shared } implies some d : Delete_Revoke | x = d.t
}

fun delete_revoke_add : set Reaction { { d : Delete_Revoke | some f : File | delete[f] and d.t in f.shared } }
fun delete_revoke_remove : set Reaction { { d : Delete_Revoke | P.revoke[d.t] } }

/*
reaction download_revoke
when
	download[t]
then
	P.revoke[t]
*/

sig Download_Revoke extends Reaction { t : Token }
fact {
	all x,y : Download_Revoke | x.t = y.t implies x = y
	all x : Token | eventually { download[x] } implies some d : Download_Revoke | x = d.t
}

fun download_revoke_add : set Reaction { { d : Download_Revoke | download[d.t] } }
fun download_revoke_remove : set Reaction { { d : Download_Revoke | P.revoke[d.t] } }

/*
reaction share_error
when
	share[f,t]
where
	f not in uploaded - trashed
then
*/

one sig Share_Error extends Reaction {}

fun share_error_add : set Reaction { { r : Share_Error | some f : File, t : Token | share[f,t] and f not in uploaded - trashed } }

/*
reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed and shared.t not in trashed
then
*/

one sig Revoke_Error extends Reaction {}
fun revoke_error_add : set Reaction { { r : Revoke_Error | some t : Token | P.revoke[t] and t not in P.accessed and shared.t not in trashed } }

// Reaction semantics

fun reactions_to_add : set Reaction { delete_revoke_add + download_revoke_add + share_error_add + revoke_error_add }
fun reactions_to_remove : set Reaction { delete_revoke_remove + download_revoke_remove }

fact {
	no reactions
	always {
		// Priority to reactions
		some reactions and some action implies some reactions & reactions_to_remove
		reactions' = (reactions - reactions_to_remove) + reactions_to_add
	}
}
