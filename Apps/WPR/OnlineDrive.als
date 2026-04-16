module Apps/WPR/OnlineDrive

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

// Projections of the state of the concepts to simplify the specification and visualization

fun registered : set User { A.registered }
fun loggedin : set User { A.loggedin }
fun trash : User -> Trash { O.owns }

// Priority of reactions over requests

fact {
    PriorityToReactions
}

// The app invariant

// Each trash can only be modified by its owner
check Invariant {
	always {
        no Reaction iff {
            trash.Trash = registered
            trash in User -> lone Trash
            all u : registered & User, t : u.trash | t.accessible = { f : File | before (not (t.delete[f] and u in loggedin) since ((t.create[f] or t.restore[f]) and u in loggedin)) }
            all u : registered & User, t : u.trash | t.trashed = { f : File | before (not ((t.restore[f] or t.empty[]) and u in loggedin) since (t.delete[f] and u in loggedin)) }
        }
	}
} for 2 but 10 Action, 2 Reaction, 2 Trash expect 0 // must set the scope of Trash as 2 otherwise a scope of 2 will apply to Concept, which will not allow trashes

// Scenarios

run Scenario1 {
    all u : User | eventually (File in u.trash.trashed and u.trash.empty[])
} for exactly 2 File, exactly 2 User, 2 Trash, 10 Action, 2 Reaction, 17 steps expect 1

run Scenario2 {
    eventually { User in registered and eventually no User & registered }
    eventually always no Reaction
} for exactly 0 File, exactly 2 User, 2 Trash, 10 Action, 2 Reaction, 11 steps expect 1
    
// Reactions

/*
reaction RegisterAcquire[u : User]
when
    A.register[u]
then
    some t : Trash | no t.accessible and no t.trashed and O.acquire[u,t]
*/

var sig RegisterAcquire extends Reaction { var u : User }
fact {	
	always all r : RegisterAcquire {
		all d : RegisterAcquire' | d.u' = r.u implies d = r
	}
}
pred RegisterAcquire[x : User] { some r : RegisterAcquire | r.u = x }

fact {
    all u : User | always {
        RegisterAcquire[u] iff {
            before {
                not (some t : Trash | no t.accessible and no t.trashed and O.acquire[u,t]) since A.register[u]
            }
        }
    }
}

/*
reaction DeleteRelease[u : User]
when
    A.delete[u]
then
    O.release[u,u.trash]
*/

var sig DeleteRelease extends Reaction { var u : User }
fact {	
    always all r : DeleteRelease {
        all d : DeleteRelease' | d.u' = r.u implies d = r
    }
}
pred DeleteRelease[x : User] { some r : DeleteRelease | r.u = x }

fact {
    all u : User | always {
        DeleteRelease[u] iff {
            before {
                not O.release[u,u.trash] since A.delete[u]
            }
        }
    }
}

// Preventions

/*
when
    O.acquire[u,t]
require
    u in registered and no t.accessible and no t.trashed and no u.trash
*/

fact {
    all u : User, t : Trash | always {
        O.acquire[u,t] implies u in registered and no t.accessible and no t.trashed and no u.trash
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
