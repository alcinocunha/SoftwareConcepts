module Apps/WPR/NoSecretsInTrash1
open Action
open Reaction

// App configuration

// Used concepts

open Concepts/Trash[File]

one sig T extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// Projections of the state of the concepts to simplify the specification and visualization

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }

// Priority of reactions over requests

fact {
	PriorityToReactions
}

// The app invariant

// Secret files cannot be in the trash
check Invariant {
	always {
		no Reaction iff {
			no Secret & trashed
		} 
	}
} for 2 but 4 Action, 1 Reaction expect 0

// Scenarios

// Without concurrent requests we cannot have more than one secret
// file in the trash, so the following scenario is impossible
run Scenario1 {
	Secret = File
	eventually Secret in trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 0	

// All files (including both secret and no secret) will be deleted
// Then a reaction will empty the trash including the non secret files
run Scenario2 {
	one Secret
	some File - Secret
	eventually File in trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 1

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

var lone sig DeleteEmpty extends Reaction { }  { all d : DeleteEmpty' | d = this }

fact {
	always {
		DeleteEmpty iff {
			some f : File | before {
				not T.empty[] since (T.delete[f] and f in Secret)
			}
		}
	}
}
