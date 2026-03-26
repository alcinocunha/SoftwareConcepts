module Apps/NoSecretsInTrash1
open Action
open Reaction

// App configuration

// Used concepts

open Concepts/Trash[File]

// Several users sharing the same trash
one sig T extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// App specific relations
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
} for 2 User, exactly 3 File, 4 Action, 1 Reaction expect 1	

// All files (including both secret and no secret) will be deleted
// Then a reaction will empty the trash including the non secret files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in trashed
	eventually always no Reaction		
} for 2 User, exactly 3 File, 4 Action, 1 Reaction expect 1

// Reactions

/*
when
	T.delete[u,f]
where
	f in Secret
then
	some u : User | T.empty[u]
*/

var lone sig DeleteEmpty extends Reaction {}

fact {
	always {
		some DeleteEmpty iff {
			some u : User, f : File | before {
				not (some u : User | T.empty[u]) since (T.delete[u,f] and f in Secret)
			}
		}
	}
}

// Preventions

/*
when
	T.restore[u,f]
require
	f not in Secret
*/

fact {
	all u : User, f : File | always {
		T.restore[u,f] implies f not in Secret
	}
}
