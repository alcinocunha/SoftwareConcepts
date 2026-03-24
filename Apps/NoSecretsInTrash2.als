module Apps/NoSecretsInTrash2
open Action[User]
open Reaction

// App configuration

// User concepts
open Concepts/Trash[User,File]

// Several users sharing the same trash, special user System will empty the trash when secrets are deleted
sig User {}
one sig System extends User {}

one sig SharedTrash extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// The app invariant

// Secret files cannot be in the trash
// Accessible files were created or restored by a normal user
// Trashed files were deleted by a normal user
check Invariant {
	always {
		no Reaction iff {
			no Secret & SharedTrash.trashed
			all f : File | f in SharedTrash.accessible iff before (not (some u : User - System | SharedTrash.delete[u,f]) since (some u : User - System | SharedTrash.create[u,f] or SharedTrash.restore[u,f]))
			all f : File - Secret | f in SharedTrash.trashed iff before (not (some u : User - System | SharedTrash.empty[u] or SharedTrash.restore[u,f]) since (some u : User - System | SharedTrash.delete[u,f]))
		} 
	}
} for 2 but 4 Action, 5 Reaction expect 1

// Scenarios

// All files are secret and will be deleted
// Then a reaction will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in SharedTrash.trashed
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 1 Reaction expect 1

// At some point a secret file is deleted when some non secret fine is in the trash
// Then a reaction will first restore the non secret files, empty the trash, and finally delete again the restored files
run Scenario2 {
	eventually (some SharedTrash.trashed - Secret and some u : User, s : Secret | SharedTrash.delete[u,s])
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 3 Reaction expect 1


// At some point a secret file is deleted when the system is already reacting to a previous secret file deletion
run Scenario3 {
	eventually (DeleteEmpty and some u : User, f : Secret | SharedTrash.delete[u,f])
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 3 Reaction expect 1


// At some point a non-secret file is deleted when the system is already reacting to a previous secret file deletion
run Scenario3 {
	eventually (DeleteEmpty and some u : User, f : File-Secret | SharedTrash.delete[u,f])
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 3 Reaction expect 1


// Reactions

/*
reaction DeleteEmpty
when
	SharedTrash.delete[u,f]
where
	u not in System and f in Secret
then
	SharedTrash.empty[System]
*/

var lone sig DeleteEmpty extends Reaction {}
pred DeleteEmpty { some DeleteEmpty }
fact {
	always {
		some DeleteEmpty iff {
			some u : User, f : File | before {
				not SharedTrash.empty[System] since (SharedTrash.delete[u,f] and u not in System and f in Secret)
			}
		}
	}
}

/*
reaction DeleteRestore[g : File]
when
	SharedTrash.delete[u,f]
where
	u not in System and f in Secret and g in SharedTrash.trashed - Secret
then
	SharedTrash.restore[System,g]
*/

var sig DeleteRestore extends Reaction { var g : File }
pred DeleteRestore [x : File] { some d : DeleteRestore | d.g = x }
fact {
	all g : File | always {
		DeleteRestore[g] iff {
			some u : User, f : File | before {
				not SharedTrash.restore[System,g] since (SharedTrash.delete[u,f] and u not in System and f in Secret and g in SharedTrash.trashed - Secret)
			}
		}
	}
}

/*
reaction DeleteDelete[g : File]
when
	SharedTrash.delete[u,f]
where
	u not in System and f not in Secret and g in SharedTrash.trashed - Secret
then
	SharedTrash.delete[System,g]
*/

var sig DeleteDelete extends Reaction { var g : File }
pred DeleteDelete [x : File] { some d : DeleteDelete | d.g = x }

fact {
	all g : File | always {
		DeleteDelete[g] iff {
			some u : User, f : File | before {
				not SharedTrash.delete[System,g] since (SharedTrash.delete[u,f] and f in Secret and g in SharedTrash.trashed - Secret)
			}
		}
	}
}

// Preventions

/*
when
	SharedTrash.create[System,f]
require
	false
*/

fact {
	all f : File | always {
		SharedTrash.create[System,f] implies false
	}
}

/*
when
	SharedTrash.delete[System,f]
require
	DeleteDelete[f]
*/

fact {
	all f : File | always {
		SharedTrash.delete[System,f] implies DeleteDelete[f]
	}
}

/*
when
	SharedTrash.restore[System,f]
require
	DeleteRestore[f] 
*/

fact {
	all f : File | always {
		SharedTrash.restore[System,f] implies DeleteRestore[f]
	}
}

/*
when
	SharedTrash.empty[System]
require
	SharedTrash.trashed in Secret
*/

fact {
	always {
		SharedTrash.empty[System] implies SharedTrash.trashed in Secret
	}
}

/*
when
	SharedTrash.delete[u,f]
require
	u not in System implies not DeleteDelete[f]
*/

fact {
	all u : User, f : File | always {
		SharedTrash.delete[u,f] implies (u not in System implies not DeleteDelete[f])
	}
}

/*
when
	SharedTrash.restore[u,f]
require
	u not in System implies f not in Secret and not DeleteRestore[f]
*/

fact {
	all u : User, f : File | always {
		SharedTrash.restore[u,f] implies (u not in System implies f not in Secret and not DeleteRestore[f])
	}
}

/*
when
	SharedTrash.empty[u]
require
	u not in System implies no Secret & SharedTrash.trashed
*/

fact {
	all u : User | always {
		SharedTrash.empty[u] implies (u not in System implies no Secret & SharedTrash.trashed)
	}
}
