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

// Priority of reactions over requests
fact {
    PriorityToReactions
}

// The outbox of the restaurant contains one message per active reservation
check Invariant {
    always {
        no Reaction iff {
            reservations = { c : Client, t : Table | some m : Message | m in Restaurant.outbox and m.content = t and m.to = c }
        }
    }
} for 2 Client, 2 Table, 3 Time, 3 Message, 9 Action, 4 Reaction expect 0

// Scenario

run Scenario {
    some c : Client | all t : Table | eventually R.use[c,t]
    eventually always no Reaction
} for 3 but exactly 3 Table, 9 Action, 2 Reaction, 16 steps expect 1

// Reactions

/*
reaction SendConfirmation[t]
when
    R.reserve[c,t]
then
    some m : Message | M.send[Restaurant,m] and m.to = c and m.content = t
*/

var sig SendConfirmation extends Reaction { var t : Table }
fact {
    always all r : SendConfirmation {
		all d : SendConfirmation' | d.t' = r.t implies d = r
	}
}
pred SendConfirmation [ y : Table ] { some d : SendConfirmation | d.t = y }

fact {
    all t : Table | always {
        SendConfirmation[t] iff some c : Client | before {
            not (some m : Message | M.send[Restaurant,m] and m.to = c and m.content = t) since R.reserve[c,t]
        }
    }
}

/*
reaction UseDelete[t]
when
    R.use[c,t]
then
    some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t
*/

var sig UseDelete extends Reaction { var t : Table }
fact {
    always all r : UseDelete {
        all d : UseDelete' | d.t' = r.t implies d = r
    }
}
pred UseDelete [ y : Table ] { some d : UseDelete | d.t = y }

fact {
    all t : Table | always {
        UseDelete[t] iff some c : Client | before {
            not (some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t) since R.use[c,t]
        }
    }
}

/*
reaction CancelDelete[t]
when
    R.cancel[c,t]
then
    some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t
*/

var sig CancelDelete extends Reaction { var t : Table }
fact {
    always all r : CancelDelete {
        all d : CancelDelete' | d.t' = r.t implies d = r
    }
}
pred CancelDelete [ y : Table ] { some d : CancelDelete | d.t = y }

fact {
    all t : Table | always {
        CancelDelete[t] iff some c : Client | before {
            not (some m : Message | M.deleteFromOutbox[Restaurant,m] and m.to = c and m.content = t) since R.cancel[c,t]
        }
    }
}

/* Preventions

// Not sure how to express the condition without referring to the reaction, which is not ideal

/*
when
	M.send[Restaurant,m]
require
	m.content in m.to.reservations and m.content not in Restaurant.outbox.content
*/

fact {
    all m : Message | always {
    	M.send[Restaurant,m] implies m.content in m.to.reservations and m.content not in Restaurant.outbox.content
    }
}

/*
when
    M.deleteFromOutbox[Restaurant,m]
require
    m.content not in m.to.reservations
*/

fact {
    all m : Message | always {
        M.deleteFromOutbox[Restaurant,m] implies m.content not in m.to.reservations
    }
}

