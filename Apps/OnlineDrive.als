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

// This app assumes reactions have priority over requests

fact {
    PriorityToReactions
}

// The design goal

// Each trash can only be modified by its owner
check Design {
	always {
        no reactions iff {
            trash in registered -> one Trash
            accessible = { t : Trash, f : File | before (not (t.delete[f] and t = loggedin.trash or (some u : User | O.acquire[u,t])) since ((t.create[f] or t.restore[f]) and t = loggedin.trash)) }
            trashed = { t : Trash, f : File | before (not ((t.restore[f] or t.empty[]) and t = loggedin.trash or (some u : User | O.acquire[u,t])) since (t.delete[f] and t = loggedin.trash)) }
        }
	}
} for 2 but 10 Action, 10 Reaction, 2 Trash expect 0 // must set the scope of Trash as 2 otherwise a scope of 2 will apply to Concept, which will not allow trashes

// Scenarios

run Scenario1 {
    all u : User | eventually (File in u.trash.trashed and u.trash.empty[])
    eventually always no reactions
} for exactly 1 File, exactly 2 User, 2 Trash, 13 Action, 6 Reaction, 13 steps expect 1

run Scenario2 {
    eventually { User in registered and eventually no User & registered }
    eventually always no reactions
} for exactly 0 File, exactly 2 User, 2 Trash, 10 Action, 6 Reaction, 11 steps expect 1
    
// Reactions

/*
reaction register_acquire
when
    A.register[u]
then
    some t : Trash | O.acquire[u,t]
*/

sig Register_Acquire extends Reaction { user : User }
fact {
    all x,y : Register_Acquire | x.user = y.user implies x = y
}
fact {
    all u : User | always {
        (some r : Register_Acquire & reactions_to_add | r.user = u) iff (A.register[u])
        (some r : Register_Acquire & reactions_to_remove | r.user = u) iff (some t : Trash | O.acquire[u,t])
    }
}

/*
reaction delete_release
when
    A.delete[u]
then
    O.release[u,u.trash]
*/

sig Delete_Release extends Reaction { user : User }
fact {
    all x,y : Delete_Release | x.user = y.user implies x = y
}
fact {
    all u : User | always {
        (some r : Delete_Release & reactions_to_add | r.user = u) iff (A.delete[u])
        (some r : Delete_Release & reactions_to_remove | r.user = u) iff (O.release[u,u.trash])
    }
}  

/*
reaction acquire_error
when
    O.acquire[u,t]
where
    u not in registered or some u.trash or some t.accessible or some t.trashed
then
    error
*/

sig Acquire_Error extends Reaction { }
fact {
    all x,y : Acquire_Error | x = y
}
fact {
    always {
        (some Acquire_Error & reactions_to_add) iff (some u : User, t : Trash | O.acquire[u,t] and (u not in registered or some u.trash or some t.accessible or some t.trashed))
        (some Acquire_Error & reactions_to_remove) iff error
    }
}

/*
reaction release_error
when
    O.release[u,t]
where
    u in registered
then
    error
*/

sig Release_Error extends Reaction { }
fact {
    all x,y : Release_Error | x = y
}
fact {
    always {
        (some Release_Error & reactions_to_add) iff (some u : User, t : Trash | O.release[u,t] and u in registered)
        (some Release_Error & reactions_to_remove) iff error
    }   
}

/*
reaction create_error
when
    t.create[f]
where
    t != loggedin.trash
then
    error
*/

sig Create_Error extends Reaction { }
fact {
    all x,y : Create_Error | x = y
}
fact {    
    always {
        (some Create_Error & reactions_to_add) iff (some t : Trash, f : File | t.create[f] and t != loggedin.trash)
        (some Create_Error & reactions_to_remove) iff error
    }  
}

/*
reaction delete_error
when
    t.delete[f]
where
    t != loggedin.trash
then
    error
*/

sig Delete_Error extends Reaction { }
fact {
    all x,y : Delete_Error | x = y
}
fact {    
    always {
        (some Delete_Error & reactions_to_add) iff (some t : Trash, f : File | t.delete[f] and t != loggedin.trash)
        (some Delete_Error & reactions_to_remove) iff error
    }  
}

/*
reaction restore_error
when
    t.restore[f]
where
    t != loggedin.trash
then
    error
*/

sig Restore_Error extends Reaction { }
fact {
    all x,y : Restore_Error | x = y
}
fact {    
    always {
        (some Restore_Error & reactions_to_add) iff (some t : Trash, f : File | t.restore[f] and t != loggedin.trash)
        (some Restore_Error & reactions_to_remove) iff error
    }
}

/*
reaction empty_error
when
    t.empty[]
where
    t != loggedin.trash
then
    error
*/

sig Empty_Error extends Reaction { }
fact {
    all x,y : Empty_Error | x = y
}
fact {    
    always {
        (some Empty_Error & reactions_to_add) iff (some t : Trash | t.empty[] and t != loggedin.trash)
        (some Empty_Error & reactions_to_remove) iff error
    }
}
