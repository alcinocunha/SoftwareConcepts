module Apps/WPR/FileSharing1
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

// Priority of reactions over requests

fact {
	PriorityToReactions
}

// The design goal

// The shared tokes are those that have been shared while the respective file was accessible
// and not deleted nor downloaded afterwards
check Design {
	always {
		no Reaction iff {
			shared = { f : File, t : Token | before (not (delete[f] or download[t]) since (share[f,t] and f in uploaded - trashed))}
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Additional properties

// Some invariants
check Invariants {
	always {
		no Reaction implies {
			shared.Token in uploaded - trashed
			accessed in revoked			
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Expected revoked value
check Revoked {
	always {
		no Reaction implies {
			P.revoked = { t : Token | before once (download[t] or some f : File | t in f.shared and delete[f]) }
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Note that the following two properties are always true, unlike in the version without priority to reactions.

// Downloaded files must be uploaded and not trashed
check DownloadedAreAccessible {
	all t : Token | always {
		download[t] implies shared.t in uploaded - trashed
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Tokens can only be accessed once
check SingleAccess {
	all t : Token | always {
		download[t] implies before historically not download[t]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Revokes only possible in reactions
check NoRevokes {
	all t : Token | always {
		no Reaction implies not P.revoke[t]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Scenarios

// A file is uploaded, shared twice, accessed, and deleted. Reactions should revoke all tokens.
run Scenario1 {
	some f : File, t,u : Token {
		upload[f]; share[f,t]; share[f,u]; download[u]; some Reaction; delete[f]
	}
	eventually always no Reaction
} for exactly 1 File, 2 Token, 7 Action, 2 Reaction expect 1

// A file is uploaded, shared, and deleted. 
// Then, when the reactions are finished one tries to access the token, which should not be possible.
run Scenario2 {
	some f : File, t : Token {
		upload[f]; share[f,t]; delete[f]; eventually download[t]
	}
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 0

// A file is uploaded and shared.
// Then one tries to revoke the token, which should not be possible.
run Scenario3 {
	some f : File, t : Token {
		upload[f]; share[f,t]; P.revoke[t]
	}
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 0

// Reactions

/*
reaction DeleteRevoke[t : Token]
when
	delete[f]
where
	t in f.shared
then
	P.revoke[t]
*/

var sig DeleteRevoke extends Reaction { var t : Token }
fact { 
	always all r : DeleteRevoke {
		all d : DeleteRevoke' | d.t' = r.t implies d = r
	}
}
pred DeleteRevoke [ x : Token ] { some r : DeleteRevoke | r.t = x }

fact {
	all t : Token | always {
		DeleteRevoke[t] iff {
			some f : File | before {
				not P.revoke[t] since (delete[f] and t in f.shared)
			}
		}
	}
}

/*
reaction DownloadRevoke[t : Token]
when
	download[t]
then
	P.revoke[t]
*/

var sig DownloadRevoke extends Reaction { var t : Token }
fact { 
	always all r : DownloadRevoke {
		all d : DownloadRevoke' | d.t' = r.t implies d = r
	}
}
pred DownloadRevoke [ x : Token ] { some r : DownloadRevoke | r.t = x }

fact {
	all t : Token | always {
		DownloadRevoke[t] iff {
			before {
				not P.revoke[t] since download[t]
			}
		}
	}
}

// Preventions

/*
when
	share[f,t]
require
	f in uploaded - trashed
*/

fact {
	all f : File, t : Token | always {
		share[f,t] implies f in uploaded - trashed
	}
}

/*
when
	P.revoke[t]
require
	t in accessed or shared.t in trashed
*/

fact {
	all t : Token | always {
		P.revoke[t] implies t in P.accessed or shared.t in trashed
	}
}
