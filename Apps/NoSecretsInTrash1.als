module Apps/NoSecretsInTrash1
open Action[User]
open Reaction

// Composed concepts

open Concepts/Trash[User,File]

// Single user app

one sig User {}

// Types

sig File {}
sig Secret extends File {}

// The app invariant

// Secret files cannot be in the trash
check Invariant {
	always {
		no Reaction iff {
			no Secret & User.trashed
		} 
	}
} for 2 but 4 Action, 1 Reaction expect 1

// Scenarios

// All files are secret and will be deleted
// Then a reaction will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in User.trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 1	

// All files (including both secret and no secret) will be deleted
// Then a reaction will empty the trash including the non secret files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in User.trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 1 Reaction expect 1

// Reactions

/*
when
	delete[User,f]
where
	f in Secret
then
	empty[User]
*/

var lone sig DeleteEmpty extends Reaction { }

fact {
	always {
		some DeleteEmpty iff {
			some f : File | before {
				not empty[User] since (delete[User,f] and f in Secret)
			}
		}
	}
}

// Preventions

/*
when
	restore[User,f]
require
	f not in Secret
*/

fact {
	all f : File | always {
		restore[User,f] implies f not in Secret
	}
}
