module Apps/NoSecretsInTrash2
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
// Non secret files are in the trash iff they were deleted by the user and not restored or emptied by the user since then
check Invariant {
	always {
		no Reaction iff {
			no Secret & User.trashed
			all f : File-Secret | f in User.trashed iff before ((not request[empty[User]] and not request[restore[User,f]]) since request[delete[User,f]])
		} 
	}
} for 2 but 4 Action, 3 Reaction expect 1

// Scenarios

// All files are secret and will be deleted
// Then a reaction will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in User.trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 3 Reaction expect 1

// All files (including both secret and no secret) will be deleted
// Then a reaction will first restore the non secret files, empty the trash, and finally delete again the restored files
run Scenario2 {
	some Secret
	some File - Secret
	eventually File in User.trashed
	eventually always no Reaction		
} for exactly 3 File, 4 Action, 3 Reaction expect 1

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

/*
when
	delete[User,f]
where
	f in Secret and g in User.trashed - Secret
then
	restore[User,g]
*/

var lone sig DeleteRestore extends Reaction { }
fact {
	always {
		some DeleteRestore iff {
			some f, g : File | before {
				not restore[User,g] since (delete[User,f] and f in Secret and g in User.trashed - Secret)
			}
		}
	}
}

/*
when
	delete[User,f]
where
	f in Secret and g in User.trashed - Secret
then
	delete[User,g]
*/

var lone sig DeleteDelete extends Reaction { }
fact {
	always {
		some DeleteDelete iff {
			some f, g : File | before {
				not delete[User,g] since (delete[User,f] and f in Secret and g in User.trashed - Secret)
			}
		}
	}
}

// Preventions

/*
when
	delete[User,f]
require
	f not in Secret implies no Secret & User.trashed
*/

fact {
	all f : File | always {
		delete[User,f] implies (f not in Secret implies no Secret & User.trashed)
	}
}

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

/*
when
	empty[User]
require
	no User.trashed & Secret or no User.trashed - Secret
*/

fact {
	always {
		empty[User] implies (no User.trashed & Secret or no User.trashed - Secret)
	}
}
