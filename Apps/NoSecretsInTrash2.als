module Apps/NoSecretsInTrash2
open Action
open Reaction

// App configuration

// User concepts
open Concepts/Trash[File]

// Several users sharing the same trash, special user System will empty the trash when secrets are deleted
sig Normal extends User {}
one sig System extends User {}

one sig T extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// App specific relations
fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }

// The app invariant

// Secret files cannot be in the trash
// Accessible files were created or restored by a normal user
// Trashed non-secret files were deleted by a normal user
check Invariant {
	always {
		no Reaction iff {
			no Secret & trashed
			all f : File | f in accessible iff before (not (some u : User - System | T.delete[u,f]) since (some u : User - System | T.create[u,f] or T.restore[u,f]))
			all f : File - Secret | f in trashed iff before (not (some u : User - System | T.empty[u] or T.restore[u,f]) since (some u : User - System | T.delete[u,f]))
		} 
	}
} for 2 but 4 Action, 5 Reaction expect 0

// Scenarios

// All files are secret and will be deleted
// Then a reaction will empty the trash
run Scenario1 {
	Secret = File
	eventually Secret in trashed
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 1 Reaction expect 1

// At some point a secret file is deleted when some non secret fine is in the trash
// Then a reaction will first restore the non secret files, empty the trash, and finally delete again the restored files
run Scenario2 {
	eventually (some trashed - Secret and some u : User, s : Secret | T.delete[u,s])
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 3 Reaction expect 1


// At some point a secret file is deleted when the system is already reacting to a previous secret file deletion
run Scenario3 {
	eventually (DeleteEmpty and some u : User, f : Secret | T.delete[u,f])
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 3 Reaction expect 1


// At some point a non-secret file is deleted when the system is already reacting to a previous secret file deletion
run Scenario4 {
	eventually (DeleteEmpty and some u : User, f : File-Secret | T.delete[u,f])
	eventually always no Reaction		
} for exactly 3 File, 2 User, 4 Action, 3 Reaction expect 1

// Reactions

/*
reaction DeleteEmpty
when
	T.delete[u,f]
where
	u not in System and f in Secret
then
	T.empty[System]
*/

var lone sig DeleteEmpty extends Reaction {}
pred DeleteEmpty { some DeleteEmpty }
fact {
	always {
		some DeleteEmpty iff {
			some u : User, f : File | before {
				not T.empty[System] since (T.delete[u,f] and u not in System and f in Secret)
			}
		}
	}
}

/*
reaction DeleteRestore[g : File]
when
	T.delete[u,f]
where
	u not in System and f in Secret and g in trashed - Secret
then
	T.restore[System,g]
*/

var sig DeleteRestore extends Reaction { var g : File }
pred DeleteRestore [x : File] { some d : DeleteRestore | d.g = x }
fact {
	all g : File | always {
		DeleteRestore[g] iff {
			some u : User, f : File | before {
				not T.restore[System,g] since (T.delete[u,f] and u not in System and f in Secret and g in trashed - Secret)
			}
		}
	}
}

/*
reaction DeleteDelete[g : File]
when
	T.delete[u,f]
where
	u not in System and f not in Secret and g in trashed - Secret
then
	T.delete[System,g]
*/

var sig DeleteDelete extends Reaction { var g : File }
pred DeleteDelete [x : File] { some d : DeleteDelete | d.g = x }

fact {
	all g : File | always {
		DeleteDelete[g] iff {
			some u : User, f : File | before {
				not T.delete[System,g] since (T.delete[u,f] and f in Secret and g in trashed - Secret)
			}
		}
	}
}

// Preventions

/*
when
	T.create[System,f]
require
	false
*/

fact {
	all f : File | always {
		T.create[System,f] implies false
	}
}

/*
when
	T.delete[System,f]
require
	DeleteDelete[f]
*/

fact {
	all f : File | always {
		T.delete[System,f] implies DeleteDelete[f]
	}
}

/*
when
	T.restore[System,f]
require
	DeleteRestore[f] 
*/

fact {
	all f : File | always {
		T.restore[System,f] implies DeleteRestore[f]
	}
}

/*
when
	T.empty[System]
require
	trashed in Secret
*/

fact {
	always {
		T.empty[System] implies trashed in Secret
	}
}

/*
when
	T.delete[u,f]
require
	u not in System implies not DeleteDelete[f]
*/

fact {
	all u : User, f : File | always {
		T.delete[u,f] implies (u not in System implies not DeleteDelete[f])
	}
}

/*
when
	T.restore[u,f]
require
	u not in System implies f not in Secret and not DeleteRestore[f]
*/

fact {
	all u : User, f : File | always {
		T.restore[u,f] implies (u not in System implies f not in Secret and not DeleteRestore[f])
	}
}

/*
when
	T.empty[u]
require
	u not in System implies no Secret & trashed
*/

fact {
	all u : User | always {
		T.empty[u] implies (u not in System implies no Secret & trashed)
	}
}
