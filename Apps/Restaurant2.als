module Apps/Restaurant2
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


// Views of the state of the concepts to simplify the specification and visualization

fun tables : set Table { R.available }
// Active reservations are those that have been reserved but not yet used
fun reservations : Client -> Table { R.reservations :> R.available }
fun inbox : User -> User -> set Message { M.inbox }
fun read : User -> User -> set Message { M.read }

// In this case it is not possible to determine exactly if there should be a reaction just by looking at the state of the concepts
// Requiring that the inbox of a client has a confirmation if before it was not deleted since they
// reserved a table will not work, because the inbox may still have previous confirmations and the
// restaurant will send a confirmation anyway
// Of course we could restrict the reaction and only send if there is no confirmation in the inbox
// but seems rather artificial

// The need for the reaction is thus not driven by an invariant, hence the implies instead of iff

check Invariant {
    always {
        no Reaction implies {
			// Restaurant will not send messages to itself
            no Restaurant.inbox[Restaurant]
        }
    }
} for 2 but 8 Action, 4 Reaction expect 0

// Scenario

run Scenario {
    some c : Client | all t : Table | eventually R.reserve[c,t]
    eventually always no Reaction
} for 2 but exactly 3 Table, 3 Message, 8 Action, 3 Reaction expect 1

// Reactions

/*
reaction SendConfirmation[t]
when
    R.reserve[c,t]
then
    some m : Message | M.send[Restaurant,c,m] and m.content.table = t
*/

var sig SendConfirmation extends Reaction { var t : Table }
pred SendConfirmation [ x : Table ] { some d : SendConfirmation | d.t = x }

fact {
    all t : Table | always {
        SendConfirmation[t] iff some c : Client | before {
            not (some m : Message | M.send[Restaurant,c,m] and m.content = t) since R.reserve[c,t]
        }
    }
}

/* Preventions

/*
when
	R.send[Restaurant,t,m]
require
	t in Client
*/

fact {
    all t : User, m : Message | always {
        M.send[Restaurant,t,m] implies t in Client
    }
}
