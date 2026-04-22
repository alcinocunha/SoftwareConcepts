module Apps/WPR/Restaurant2
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Reservation[Client,Table]
open Concepts/Messaging[User,Table]

one sig R extends Reservation {}
one sig M extends Messaging {}

// Types

abstract sig User {}
sig Client extends User {}
one sig Restaurant extends User {}

sig Table {}

// Only the restaurant can send messages
fact {
    Message.from = Restaurant
}

// Views of the state of the concepts to simplify the specification and visualization

fun tables : set Table { R.available }
// Active reservations are those that have been reserved but not yet used
fun reservations : Client -> Table { R.reservations :> R.available }
fun inbox : User -> set Message { M.inbox }
fun read : User -> set Message { M.read }
fun outbox : User -> set Message { M.outbox }

// This app assumes reactions have priority over requests
fact {
    PriorityToReactions
}

// The design goal

// The outbox of the restaurant contains one message per active reservation
check Design {
    always {
        no reactions iff {
            reservations = ~(Restaurant.outbox <: to).content
            all t : Table | lone Restaurant.outbox & content.t
        }
    }
} for 2 Client, 2 Table, 3 Time, 3 Message, 10 Action, 10 Reaction expect 0

// Scenario

run Scenario {
    some c : Client | all t : Table | eventually R.use[c,t]
    eventually always no reactions
} for 3 but exactly 2 Table, 10 Action, 10 Reaction, 11 steps expect 1

// Reactions

/*
reaction send_confirmation
when
    R.reserve[c,t]
then
    some m : Message | M.send[Restaurant,m] and m.to = c and m.content = t
*/

sig Send_Confirmation extends Reaction { client : Client, table : Table }
fact {
    all x,y : Send_Confirmation | x.client = y.client and x.table = y.table implies x = y
}
fact {
    all c : Client, t : Table | always {
        (some r : Send_Confirmation & reactions_to_add | r.client = c and r.table = t) iff (R.reserve[c,t])
        (some r : Send_Confirmation & reactions_to_remove | r.client = c and r.table = t) iff (some m : Message | M.send[Restaurant,m] and m.to = c and m.content = t)
    }
}   

/*
reaction use_delete
when
    R.use[c,t]
then
    some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t
*/

sig Use_Delete extends Reaction { client : Client, table : Table }
fact {
    all x,y : Use_Delete | x.client = y.client and x.table = y.table implies x = y
}
fact {
    all c : Client, t : Table | always {
        (some r : Use_Delete & reactions_to_add | r.client = c and r.table = t) iff (R.use[c,t])
        (some r : Use_Delete & reactions_to_remove | r.client = c and r.table = t) iff (some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t)
    }
}

/*
reaction cancel_delete
when
    R.cancel[c,t]
then
    some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t
*/

sig Cancel_Delete extends Reaction { client : Client, table : Table }
fact {
    all x,y : Cancel_Delete | x.client = y.client and x.table = y.table implies x = y
}
fact {
    all c : Client, t : Table | always {
        (some r : Cancel_Delete & reactions_to_add | r.client = c and r.table = t) iff (R.cancel[c,t])
        (some r : Cancel_Delete & reactions_to_remove | r.client = c and r.table = t) iff (some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t)
    }
}

/*
reaction send_error
when
	M.send[Restaurant,m]
where
	m.content not in m.to.reservations or m.content in Restaurant.outbox.content
then
    error
*/

sig Send_Error extends Reaction { }
fact {
    all x,y : Send_Error | x = y
}
fact {
    always {
        (some Send_Error & reactions_to_add) iff (some m : Message | M.send[Restaurant,m] and (m.content not in m.to.reservations or m.content in Restaurant.outbox.content))
        (some Send_Error & reactions_to_remove) iff error
    }
}

/*
reaction delete_error
when
    M.deleteFromOutbox[Restaurant,m]
where
    m.content in m.to.reservations
then
    error
*/

sig Delete_Error extends Reaction { }
fact {
    all x,y : Delete_Error | x = y
}
fact {    
    always {
        (some Delete_Error & reactions_to_add) iff (some m : Message | M.deleteFromOutbox[Restaurant,m] and m.content in m.to.reservations)
        (some Delete_Error & reactions_to_remove) iff error
    }
}  

