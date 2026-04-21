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

// This app assumes reactions have priority over requests

fact {
	PriorityToReactions
}

// The design goal

// Secret files cannot be in the trash
check Design {
	always {
		no reactions iff {
			no Secret & trashed
		} 
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// All files (including both secret and no secret) will be deleted
// Then a reaction will empty the trash including the non secret files
run Scenario1 {
	one Secret
	some File - Secret
	eventually File in trashed
	eventually always no reactions		
} for exactly 3 File, 10 Action, 10 Reaction expect 1

// Without concurrent requests we cannot have more than one secret
// file in the trash, so the following scenario is impossible
run Scenario2 {
	Secret = File
	eventually Secret in trashed
	eventually always no reactions		
} for exactly 3 File, 10 Action, 10 Reaction expect 0	

// Reactions

/*
reaction delete_empty
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]
*/

sig Delete_Empty extends Reaction {}
fact {
	all x,y : Delete_Empty | x = y
}
fact {
	always {
		some Delete_Empty & reactions_to_add iff some f : File | T.delete[f] and f in Secret
		some Delete_Empty & reactions_to_remove iff T.empty[]
	}
}
