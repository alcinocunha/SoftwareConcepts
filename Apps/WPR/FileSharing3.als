module Apps/WPR/FileSharing3
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
pred download[t : Token] { P.access[t] }

// This app assumes reactions have priority over requests

fact {
	PriorityToReactions
}

// The design goal

// The shared tokens are those that were created for uploaded files and not downloaded afterwards
// The uploaded files are those that were uploaded and not downloaded afterwards
// The shared files are exactly the same as the uploaded ones
check Design {
	always {
		no reactions iff {
			no T.trashed
			P.revoked = P.accessed
			shared in T.accessible -> one Token
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Additional properties

// Expected uploaded value
check Uploaded {
	always {
		no reactions implies {
			uploaded = { f : File | before (not (some t : Token | t in f.shared and download[t]) since upload[f]) }
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Expected revoked value
check Revoked {
	always {
		no reactions implies {
			P.revoked = { t : Token | before once download[t] }
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

// A file is uploaded, which will be automatically shared. 
// Then it is downloaded and the file will be deleted and the trash emptied.
run Scenario1 {
	some f : File, t : Token {
		upload[f]
		eventually (t in f.shared and download[t])
	}
	eventually always no reactions
} for exactly 1 File, exactly 1 Token, 10 Action, 10 Reaction expect 1

// A file is uploaded and deleted, which should not be possible
run Scenario2 {
	some f : File {
		upload[f]; T.delete[f]
	}
	eventually always no reactions
} for exactly 1 File, exactly 1 Token, 10 Action, 10 Reaction expect 0


// Reactions

/*
reaction create_share
when
	T.create[f]
then
	some t : Token | P.share[f,t]
*/

sig Create_Share extends Reaction { file : File }
fact {
	all x,y : Create_Share | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some s : Create_Share & reactions_to_add | s.file = f) iff T.create[f]
		(some s : Create_Share & reactions_to_remove | s.file = f) iff (some t : Token | P.share[f,t])
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
reaction access_delete
when
	P.access[t]
where
	t in f.shared
then
	T.delete[f]
*/

sig Access_Delete extends Reaction { file : File }
fact {
	all x,y : Access_Delete | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some r : Access_Delete & reactions_to_add | r.file = f) iff (some t : Token | P.access[t] and t in f.shared)
		(some r : Access_Delete & reactions_to_remove | r.file = f) iff T.delete[f]
	}
}

/*
reaction access_empty
when
	P.access[t]
then
	T.empty[]
*/
	
sig Access_Empty extends Reaction { }
fact {
	all x,y : Access_Empty | x = y
}
fact {
	always {
		some Access_Empty & reactions_to_add iff (some t : Token | P.access[t])
		some Access_Empty & reactions_to_remove iff T.empty[]
	}
}

/*
reaction share_error
when
	P.share[f,t]
where
	f not in uploaded or some f.shared
then
	error
*/

sig Share_Error extends Reaction { }
fact {
	all x,y : Share_Error | x = y
}
fact {
	always {
		some Share_Error & reactions_to_add iff (some f : File, t : Token | P.share[f,t] and (f not in uploaded or some f.shared))
		some Share_Error & reactions_to_remove iff error
	}
}

/*
reaction delete_error
when
	T.delete[f]
where
	some f.shared and s.shared not in P.accessed
then
	error
*/

sig Delete_Error extends Reaction { }
fact {
	all x,y : Delete_Error | x = y
}
fact {
	always {
		some Delete_Error & reactions_to_add iff (some f : File | T.delete[f] and (some f.shared and f.shared not in P.accessed))
		some Delete_Error & reactions_to_remove iff error
	}
}

/*
reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed  
then
	error
*/

sig Revoke_Error extends Reaction { }
fact {
	all x,y : Revoke_Error | x = y
}
fact {
	always {
		some Revoke_Error & reactions_to_add iff (some t : Token | P.revoke[t] and t not in P.accessed)
		some Revoke_Error & reactions_to_remove iff error
	}
}
