module Apps/OnlineDrive

open Action
open Reaction

// App configuration

// Used concepts

open Concepts/Trash[File]
open Concepts/WebApp[User]
open Concepts/Owning[User,Trash]

// One web app with where each user will own their own trash

one sig A extends WebApp {}
one sig O extends Owning {}

// Types

sig User {}
sig File {}

// App specific relations

fun registered : set User { A.registered }
fun loggedin : set User { A.loggedin }
fun trash : User -> Trash { O.owns }

// The app invariant

// Each trash can only be modified by its owner
check Invariant {
	always {
        no Reaction iff {
            trash.Trash = registered
            some TrashAction implies trash.(TrashAction.c) in loggedin
        }
	}
} for 2 but 10 Action, 2 Reaction, 2 Trash expect 0 // must set the scope of Trash as 2 otherwise a scope of 2 will apply to Concept, which will not allow trashes

// Scenarios

run Scenario1 {
    all u : User | eventually (File in u.trash.trashed and u.trash.empty)
} for exactly 2 File, exactly 2 User, 2 Trash, 10 Action, 2 Reaction, 17 steps expect 1

run Scenario2 {
    eventually { User in registered and eventually no User & registered }
    eventually always no Reaction
} for exactly 0 File, exactly 2 User, 2 Trash, 10 Action, 2 Reaction, 11 steps expect 1
    
// Reactions

/*
reaction RegisterAcquire
when
    A.register[u]
then
    some t : Trash | O.acquire[u,t]
*/

var lone sig RegisterAcquire extends Reaction {} 

fact {
    always {
        some RegisterAcquire iff {
            some u : User | before {
                not (some t : Trash | O.acquire[u,t]) since A.register[u]
            }
        }
    }
}


/*
reaction DeleteRelease
when
    A.delete[u]
then
    O.release[u,u.trash]
*/

var lone sig DeleteRelease extends Reaction {} 

fact {
    always {
        some DeleteRelease iff {
            some u : User | before {
                not O.release[u,u.trash] since A.delete[u]
            }
        }
    }
}

// Preventions

/*
when
    A.login[u]
require
    some u.trash
*/

fact {
    all u : User | always {
        A.login[u] implies some u.trash
    }
}

/*
when
    O.acquire[u,t]
require
    u in registered
*/

fact {
    all u : User, t : Trash | always {
        O.acquire[u,t] implies u in registered
    }
}

/*
when
    O.release[u,t]
require
    u not in registered
*/

fact {
    all u : User, t : Trash | always {
        O.release[u,t] implies u not in registered
    }
}

/*
when
    A.register[u]
require
    no u.trash
*/

fact {
    all u : User | always {
        A.register[u] implies no u.trash
    }
}

/*
when
    t.create[f]
require
    t = loggedin.trash
*/

fact {
    all t : Trash, f : File | always {
        t.create[f] implies t = loggedin.trash
    }
}

/*
when
    t.delete[f]
require
    t = loggedin.trash
*/

fact {
    all t : Trash, f : File | always {
        t.delete[f] implies t = loggedin.trash
    }
}

/*
when
    t.restore[f]
require
    t = loggedin.trash
*/

fact {
    all t : Trash, f : File | always {
        t.restore[f] implies t = loggedin.trash
    }
}

/*
when
    t.empty[]
require
    t = loggedin.trash
*/

fact {
    all t : Trash| always {
        t.empty[] implies t = loggedin.trash
    }
}
