module Apps/Restaurant
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Reservation[Client,Table]
open Concepts/Label[Table,Reserved]

one sig R extends Reservation {}
one sig L extends Label {}

// Types

sig Client {}

sig Table {}
one sig Reserved {}

// App specific relations

fun tables : set Table { R.available }
fun reservations : Client -> Table { R.reservations }
fun reserved : set Table { L.labels.Reserved }

// The app invariant

// Reserved tables are labeled as Reserved
check Invariant {
	always {
		no Reaction iff {
			Client.reservations = reserved
		}
	}
} for 2 Table, 2 Client, 8 Action, 3 Reaction expect 0

// Scenarios

// All tables are reserved and used by some client
// Then a reaction will add and later remove the reserved sign
run Scenario {
	eventually always no Reaction
	all t : Table | eventually R.use[Client,t]
} for exactly 1 Client, exactly 2 Table, 8 Action, 3 Reaction, 11 steps expect 1

// Reactions

/*
when
	R.reserve[c,t]
then
	L.affix[t,Reserved] or R.cancel[c,t]
*/

var lone sig ReserveAffixOrCancel extends Reaction { }

fact {
	always {
		some ReserveAffixOrCancel iff {
			some c : Client, t : Table | before {
				not (L.affix[t,Reserved] or R.cancel[c,t]) since R.reserve[c,t]
			}
		}
	}
}

/*
when
	R.cancel[c,t]
where
	t in reserved
then
	L.detach[t,Reserved]
*/

var lone sig CancelDetach extends Reaction { }

fact {
	always {
		some CancelDetach iff {
			some c : Client, t : Table | before {
				not L.detach[t,Reserved] since (R.cancel[c,t] and t in reserved)
			}
		}
	}
}

/*
when
	R.use[c,t]
then
	L.detach[t,Reserved]
*/

var lone sig UseDetach extends Reaction { }

fact {
	always {
		some UseDetach iff {
			some c : Client, t : Table | before {
				not L.detach[t,Reserved] since R.use[c,t]
			}
		}
	}
}

// Preventions

/*
when
	L.affix[t,Reserved]
require
	t in Client.reservations
*/

fact {
	all t : Table | always {
		L.affix[t,Reserved] implies t in Client.reservations
	}
}

/*
when
	L.detach[t,Reserved]
require
	t not in Client.reservations
*/

fact {
	all t : Table | always {
		L.detach[t,Reserved] implies t not in Client.reservations
	}
}

/*
when
	L.clear[t]
require
	false
*/

fact {
	all t : Table | always {
		L.clear[t] implies false
	}
}

/*
when
	R.use[c,t]
require
	t in reserved
*/

fact {
	all c : Client, t : Table | always {
		R.use[c,t] implies t in reserved
	}
}

/*
when
	R.reserve[c,t]
require
	t not in reserved
*/

fact {
	all c : Client, t : Table | always {
		R.reserve[c,t] implies t not in reserved
	}
}
