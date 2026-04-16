module Apps/WOPR/FileSharing3
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

// The design goal

// The shared tokens are those that were created for uploaded files and not downloaded afterwards
// The uploaded files are those that were uploaded and not downloaded afterwards
// The shared files are exactly the same as the uploaded ones
check Design {
	always {
		no Reaction iff {
			uploaded = { f : File | before (not (some t : Token | t in f.shared and download[t]) since upload[f]) }
			shared.Token = uploaded
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Additional properties

// Some invariants
check Invariants {
	always {
		no Reaction implies {
			P.revoked = P.accessed
			no trashed & File
			shared in File -> lone Token
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Expected revoked value
check Revoked {
	always {
		no Reaction implies {
			P.revoked = { t : Token | before once download[t] }
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Downloaded files must be uploaded and not trashed
check DowloadedAreAccessible {
	all t : Token | always {
		no Reaction implies {
			download[t] implies shared.t in uploaded - trashed
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Tokens can only be accessed once
check SingleAccess {
	all t : Token | always {
		no Reaction implies {
			download[t] implies before historically not download[t]
		}
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Revokes only possible in reactions
check NoRevokes {
	all t : Token | always {
		no Reaction implies not P.revoke[t]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Shares only possible in reactions
check NoShares {
	all f : File, t : Token | always {
		no Reaction implies not P.share[f,t]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Empty only possible in reactions
check NoEmpties {
	always {
		no Reaction implies not T.empty[]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Deletes only possible in reactions
check NoDeletes {
	all f : File | always {
		no Reaction implies not T.delete[f]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Restores only posssible during reactions
check NoRestores {
	all f : File | always {
		no Reaction implies not T.restore[f]
	}
} for 2 but 7 Action, 4 Reaction expect 0

// Scenarios

// A file is uploaded, which will be automatically shared. 
// Then it is dowloaded and the file will be deleted and the trash emptied.
run Scenario1 {
	some f : File, t : Token {
		upload[f]
		eventually (t in f.shared and download[t])
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 4 Reaction expect 1

// A file is uploaded and deleted, which should not be possible
run Scenario2 {
	some f : File {
		upload[f]; T.delete[f]
	}
} for exactly 1 File, exactly 1 Token, 7 Action, 2 Reaction expect 0


// Reactions

/*
reaction UploadShare[f : File]
when
	upload[f]
then
	some t : Token | P.share[f,t]
*/

var sig UploadShare extends Reaction { var f : File }
pred UploadShare[x : File] { some r : UploadShare | r.f = x }

fact {
	all f : File | always {
		UploadShare[f] iff {
			before (not (some t : Token | P.share[f,t]) since upload[f])
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

/*
reaction DownloadDelete[f : File]
when
	download[t]
where
	t in f.shared and f in uploaded - trashed
then
	T.delete[f]
*/
	
var sig DownloadDelete extends Reaction { var f : File }
pred DownloadDelete [ x : File ] { some r : DownloadDelete | r.f = x }

fact {
	all f : File | always {
		DownloadDelete[f] iff {
			some t : Token | before {
				not T.delete[f] since (download[t] and t in f.shared and f in uploaded - trashed)
			}
		}
	}
}

/*
reaction DownloadEmpty[f : File]
when
	download[t]
where
	t in f.shared and f in uploaded - trashed
then
	T.empty[]
*/
	
var sig DownloadEmpty extends Reaction { var f : File }
pred DownloadEmpty [ x : File ] { some r : DownloadEmpty | r.f = x }

fact {
	all f : File | always {
		DownloadEmpty[f] iff {
			some t : Token | before {
				not T.empty[] since (download[t] and t in f.shared and f in uploaded - trashed)
			}
		}
	}
}

// Preventions 

/*
when
	P.share[f,t]
require
	f in uploaded - trashed and no f.shared
*/

fact {
	all f : File, t : Token | always {
		P.share[f,t] implies f in uploaded - trashed and no f.shared
	}
}

/*
when
	T.delete[f]
require
	some f.shared and f.shared in P.accessed 
*/

fact {
	all f : File | always {
		T.delete[f] implies some f.shared and f.shared in P.accessed  
	}
}

/*
when
	P.revoke[t]
require
	t in P.accessed  
*/

fact {
	all t : Token | always {
		P.revoke[t] implies t in P.accessed  
	}
}

/*
when
	upload[f]
require
	no f.shared
*/

fact {
	all f : File | always {
		upload[f] implies no f.shared
	}
}

