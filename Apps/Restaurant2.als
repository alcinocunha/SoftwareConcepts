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
fun inbox : User -> set Message { M.inbox }
fun read : User -> set Message { M.read }

// In this case it is not possible to determine exactly if there should be a reaction just by looking at the state of the concepts
// Determining what should be the state of client's inboxes seems to require counting events, which is not possible in temporal logic

// The need for the reaction is thus not driven by an invariant, hence the implies instead of a iff

check Invariant {
    always {
        no Reaction implies {
			// Restaurant will not send messages to itself
            no Restaurant.inbox.from & Restaurant
            // The following is the best we can say about client's inboxes?
            all c : Client, m : Message | m in c.inbox and m.from = Restaurant implies before (not M.delete[c,m] since R.reserve[c,m.content])
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
reaction SendConfirmation[c,t]
when
    R.reserve[c,t]
then
    some m : Message | M.send[Restaurant,m] and m.to = c and m.content.table = t
*/

var sig SendConfirmation extends Reaction { var c : Client, var t : Table }
pred SendConfirmation [ x : Client, y : Table ] { some d : SendConfirmation | d.c = x and d.t = y }

fact {
    all c : Client, t : Table | always {
        SendConfirmation[c,t] iff before {
            not (some m : Message | M.send[Restaurant,m] and m.to = c and m.content = t) since R.reserve[c,t]
        }
    }
}

/* Preventions

// Not sure how to express the condition without referring to the reaction, which is not ideal

/*
when
	R.send[Restaurant,m]
require
	SendConfirmation[m.to,m.content]
*/

fact {
    all m : Message | always {
        M.send[Restaurant,m] implies SendConfirmation[m.to,m.content]
    }
}