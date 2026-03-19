module Apps/NoSecretsInTrash1

// Composed concepts

open Concepts/Trash[File]

sig File {}
sig Secret extends File {}

// The app invariant

// Secret files cannot be in the trash
check Invariant {
	always {
		not syncing iff {
			no Secret & trashed
		} 
	}
} for 2 but 4 Action

// Scenarios

// All files are secret and will be deleted
// Syncronization will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in trashed
	eventually always not syncing		
} for exactly 3 File, 4 Action

// All files (including both secret and no secret) will be deleted
// Syncronization will empty the trash including the non secret files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in trashed
	eventually always not syncing		
} for exactly 3 File, 4 Action

// When is the app syncing

pred syncing {
	sync_delete
}

// For visualization only
one sig Syncing {}
fun syncing : Syncing { { s : Syncing | syncing } } 

// Synchronization rules

/*
when
	delete[f]
where
	f in Secret
then
	empty
*/

pred sync_delete {
	some f : File | before {
		not empty since (delete[f] and f in Secret)
	}
}

/*
when
	restore[f]
require
	f not in Secret
*/

fact {
	all f : File | always {
		restore[f] implies f not in Secret
	}
}
