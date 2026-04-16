module Apps/WPR/NoSecretsInTrash2
open Action
open Reaction

// App configuration

// User concepts
open Concepts/Trash[File]

one sig T extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// Priority of reactions over requests

fact {
	PriorityToReactions
}

// Projections of the state of the concepts to simplify the specification and visualization

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }

// The app invariant

// Secret files cannot be in the trash
// Accessible files were created or restored by a normal user
// Trashed non-secret files were deleted by a normal user
check Invariant {
	always {
		no Reaction iff {
			no Secret & trashed
			accessible = { f : File | before (not T.delete[f] since (T.create[f] or (T.restore[f] and no Secret & trashed))) }
		} 
	}
} for 2 but 4 Action, 5 Reaction expect 0

// Scenarios

// Without concurrent requests we cannot have more than one secret
// file in the trash, so the following scenario is impossible
run Scenario1 {
	Secret = File
	eventually Secret in trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 0

// At some point a secret file is deleted when some non secret fine is in the trash
// Then a reaction will first restore the non secret files, empty the trash, and finally delete again the restored files
run Scenario2 {
	eventually (some trashed - Secret and some s : Secret | T.delete[s])
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 3 Reaction expect 1

// Reactions

/*
reaction DeleteEmpty
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]
*/

var lone sig DeleteEmpty extends Reaction { } 
fact {
	always all r : DeleteEmpty {
		all d : DeleteEmpty' | d = r
	}
}
pred DeleteEmpty { some DeleteEmpty }
fact {
	always {
		DeleteEmpty iff {
			some f : File | before {
				not T.empty[] since (T.delete[f] and f in Secret)
			}
		}
	}
}

/*
reaction DeleteRestore[g : File]
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.restore[g]
*/

var sig DeleteRestore extends Reaction { var g : File } 
fact { 
	always all r : DeleteRestore {
		all d : DeleteRestore' | d.g' = r.g implies d = r
	}
}
pred DeleteRestore [x : File] { some d : DeleteRestore | d.g = x }
fact {
	all g : File | always {
		DeleteRestore[g] iff {
			some f : File | before {
				not T.restore[g] since (T.delete[f] and f in Secret and g in trashed - Secret)
			}
		}
	}
}

/*
reaction DeleteDelete[g : File]
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.delete[g]
*/

var sig DeleteDelete extends Reaction { var g : File } 
fact { 
	always all r : DeleteDelete {
		all d : DeleteDelete' | d.g' = r.g implies d = r
	}
}
pred DeleteDelete [x : File] { some d : DeleteDelete | d.g = x }

fact {
	all g : File | always {
		DeleteDelete[g] iff {
			some f : File | before {
				not T.delete[g] since (T.delete[f] and f in Secret and g in trashed - Secret)
			}
		}
	}
}

// Preventions

/*
when
	T.empty[]
require
	no trashed - Secret
*/

fact {
	always {
		T.empty[] implies no trashed - Secret
	}
}