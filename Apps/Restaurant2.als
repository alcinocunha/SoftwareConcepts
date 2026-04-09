module Apps/Restaurant2
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Reservation[Client,Table]
open Concepts/Email[User,Content]

one sig R extends Reservation {}
one sig E extends Email {}

// Types

abstract sig User {}
sig Client extends User {}
one sig Owner extends User {}

sig Table {}

abstract sig Content {}
one sig Request extends Content {}
one sig Full extends Content {}

// Generator axiom to ensure all possible messages exist
fact Generator {
    all c : Client | some m : Message | m.to = Owner and m.from = c and m.content = Request
    all c : Client | some m : Message | m.from = Owner and m.to = c and m.content = Full
}

// Views of the state of the concepts to simplify the specification and visualization

fun tables : set Table { R.available }
fun reservations : Client -> Table { R.reservations }
fun inbox : User -> set Message { E.inbox }
fun read : User -> set Message { E.read }

// The app invariant

check Invariant {
    always {
        no Reaction iff {
            // Owner receives reservation requests and cancellation requests from clients, 
            // and clients receive confirmations and rejections from the owner
            inbox[Owner] in content.Request & from.Client
            inbox[Client] in content.Full & from.Owner
            // The reserved tables are exactly those read messages kept in the inbox of the owner
			User <: reservations.Table in read[Owner].from
            read[Owner] <: from.reservations in read[Owner] lone -> one Table
            // Expected content of user inboxes, must contain a reply to every unfulfilled request
            all c : Client | inbox[c] = { m : Message | before (not E.delete[c,m] since (some r : from.c | E.read[Owner,r] and no Table - Client.reservations)) }
        }
    }
} for 3 but 8 Action, 3 Reaction expect 0

// Reactions

/*
reaction ReadRequest[r]
when
    E.read[Owner, r]
then
    (some t : Table | R.reserve[r.from, t]) or (some m : Message | E.send[Owner, m] and m.to = r.from and m.content = Full)
*/

var sig ReadRequest extends Reaction { var r : Message }
pred ReadRequest [ x : Message ] { some d : ReadRequest | d.r = x }

fact {
    all r : Message | always {
        ReadRequest[r] iff before {
            not ((some t : Table | R.reserve[r.from, t]) or (some m : Message | E.send[Owner, m] and m.to = r.from and m.content = Full)) since E.read[Owner,r]
        }
    }
}

/*
reaction DeleteRequestFull[r]
when
    E.send[Owner, r]
then
    E.delete[Owner, r]
*/

var sig DeleteRequestFull extends Reaction { var r : Message }
pred DeleteRequestFull [ x : Message ] { some d : DeleteRequestFull | d.r = x }

fact {
    all r : Message | always {
        DeleteRequestFull[r] iff before {
            not E.delete[Owner, r] since E.send[Owner, r]
        }
    }
}

/*
reaction DeleteRequestUse[t]
when
    R.use[c, t]
then
    some r : from.c | E.delete[Owner, r]
*/

var sig DeleteRequestUse extends Reaction { var t : Table }
pred DeleteRequestUse [ x : Table ] { some d : DeleteRequestUse | d.t = x }

fact {
    all t : Table | always {
        DeleteRequestUse[t] iff some c : Client | before {
            not (some r : from.c | E.delete[Owner, r]) since R.use[c,t]
        }
    }
}


// Preventions

/*
when
    E.send[c, m]
require
    c in Client implies m.content = Request and m.to = Owner
*/

fact {
    all c : User, m : Message | always {
        E.send[c,m] implies (c in Client implies m.content = Request and m.to = Owner)
    }
}

/*
when
    E.send[Owner, m]
require
    m.content = Full and some from.(m.to) & read[Owner] and no Table - Client.reservations 
*/

fact {
    all m : Message | always {
        E.send[Owner,m] implies {
            m.content = Full and some from.(m.to) & read[Owner] and no Table - Client.reservations 
        }
    }
}

/*
when
    R.reserve[c, t]
require
    some read[Owner] & from.c
*/

fact {
    all c : Client, t : Table | always {
        R.reserve[c,t] implies some read[Owner] & from.c
    }
}

/*
when
    E.delete[Owner, r]
require
    no r.from.reservations no Table - Client.reservations
*/

fact {
    all r : Message | always {
        E.delete[Owner,r] implies no r.from.reservations and no Table - Client.reservations
    }
}

/*
when
    R.cancel[c,t]
require
    false
*/

fact {
    all c : Client, t : Table | always {
        R.cancel[c,t] implies false
    }
}
