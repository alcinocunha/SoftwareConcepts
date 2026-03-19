module Apps/NoSecretsInTrash2

// Composed concepts

open Concepts/Trash[File]

sig File {}
sig Secret extends File {}

// The app invariant

let request[a] {a and not syncing}

// Secret files cannot be in the trash
// Non secret files are in the trash iff they were deleted by the user and not restored or emptied by the user since then
check Invariant {
	always {
		not syncing iff {
			no Secret & trashed
			all f : File-Secret | f in trashed iff before ((not request[empty] and not request[restore[f]]) since request[delete[f]])
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
// Syncronization will first restore the non secret files, then empty the trash, and then delete again the restored files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in trashed
	eventually always not syncing		
} for exactly 3 File, 4 Action


// When is the app syncing

pred syncing {
	sync_delete_empty or sync_delete_restore or sync_delete_delete
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

pred sync_delete_empty {
	some f : File | before {
		not empty since (delete[f] and f in Secret)
	}
}

/*
when
	delete[f]
where
	f in Secret and g in trashed-Secret
then
	restore[g]
*/

pred sync_delete_restore {
	some f, g : File | before {
		not restore[g] since (delete[f] and f in Secret and g in trashed-Secret)
	}
}

/*
when
	delete[f]
where
	f in Secret and g in trashed-Secret
then
	delete[g]
*/

pred sync_delete_delete {
	some f, g : File | before {
		not delete[g] since (delete[f] and f in Secret and g in trashed-Secret)
	}
}

/*
when
	delete[f]
requires
	f not in Secret implies no Secret & trashed
*/

fact {
	all f : File | always {
		delete[f] implies (f not in Secret implies no Secret & trashed)
	}
}

/*
when
	restore[f]
requires
	f not in Secret
*/

fact {
	all f : File | always {
		restore[f] implies f not in Secret
	}
}

/*
when
	empty
require
	no trashed & Secret or no trashed - Secret
*/

fact {
	always {
		empty implies (no trashed & Secret or no trashed - Secret)
	}
}
