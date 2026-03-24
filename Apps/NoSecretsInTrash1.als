module Apps/NoSecretsInTrash1
open Action[User]
open Reaction

// App configuration

// Used concepts

open Concepts/Trash[User,File]

// Several users sharing the same trash
sig User {}
one sig SharedTrash extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// The app invariant

// Secret files cannot be in the trash
check Invariant {
	always {
		no Reaction iff {
			no Secret & SharedTrash.trashed
		} 
	}
} for 2 but 4 Action, 1 Reaction expect 0

// Scenarios

// All files are secret and will be deleted
// Then a reaction will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in SharedTrash.trashed
	eventually always no Reaction		
} for 2 User, exactly 3 File, 4 Action, 1 Reaction expect 1	

// All files (including both secret and no secret) will be deleted
// Then a reaction will empty the trash including the non secret files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in SharedTrash.trashed
	eventually always no Reaction		
} for 2 User, exactly 3 File, 4 Action, 1 Reaction expect 1

// Reactions

/*
when
	SharedTrash.delete[u,f]
where
	f in Secret
then
	some u : User | SharedTrash.empty[u]
*/

var lone sig DeleteEmpty extends Reaction {}

fact {
	always {
		some DeleteEmpty iff {
			some u : User, f : File | before {
				not (some u : User | SharedTrash.empty[u]) since (SharedTrash.delete[u,f] and f in Secret)
			}
		}
	}
}

// Preventions

/*
when
	SharedTrash.restore[u,f]
require
	f not in Secret
*/

fact {
	all u : User, f : File | always {
		SharedTrash.restore[u,f] implies f not in Secret
	}
}
