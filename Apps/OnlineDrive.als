module Apps/OnlineDrive

open Action[User]
open Reaction

// App configuration

// Used concepts

open Concepts/Trash[User,File]

// Several users each with their own trash
sig User {
    trash : set Trash
}
fact { trash in User one -> one Trash }

// Items are files
sig File {}

// The app invariant

// Each trash can only be modified by its owner
check Invariant {
	always {
		no Reaction iff {
            all u : User, f : File | f in u.trash.accessible iff before (not u.trash.delete[u,f] since (u.trash.create[u,f] or u.trash.restore[u,f]))
            all u : User, f : File | f in u.trash.trashed iff before (not (u.trash.empty[u] or u.trash.restore[u,f]) since u.trash.delete[u,f])
		} 
	}
} for exactly 2 User, exactly 2 Trash, 2 File, 4 Action, 0 Reaction expect 0

// Scenarios

run Scenario1 {
    some u : User | eventually (File in u.trash.trashed and u.trash.empty[u])
} for exactly 3 File, 1 User, 1 Trash, 4 Action, 0 Reaction expect 1

// Preventions

/*
when
    t.create[u,f]
require
    t = u.trash
*/

fact {
    all t : Trash, u : User, f : File | always {
        t.create[u,f] implies t = u.trash
    }
}

/*
when
    t.delete[u,f]
require
    t = u.trash
*/

fact {
    all t : Trash, u : User, f : File | always {
        t.delete[u,f] implies t = u.trash
    }
}

/*
when
    t.restore[u,f]
require
    t = u.trash
*/

fact {
    all t : Trash, u : User, f : File | always {
        t.restore[u,f] implies t = u.trash
    }
}

/*
when
    t.empty[u]
require
    t = u.trash
*/

fact {
    all t : Trash, u : User | always {
        t.empty[u] implies t = u.trash
    }
}
