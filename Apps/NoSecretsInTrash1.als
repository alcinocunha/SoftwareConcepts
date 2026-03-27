module Apps/NoSecretsInTrash1
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

// All files are secret and will be deleted
// Then a reaction will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 1	

// All files (including both secret and no secret) will be deleted
// Then a reaction will empty the trash including the non secret files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 1

// Reactions

/*
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]
*/

var lone sig DeleteEmpty extends Reaction {}

fact {
	always {
		some DeleteEmpty iff {
			some f : File | before {
				not T.empty[] since (T.delete[f] and f in Secret)
			}
		}
	}
}

// Preventions

/*
when
	T.restore[f]
require
	f not in Secret
*/

fact {
	all f : File | always {
		T.restore[f] implies f not in Secret
	}
}
