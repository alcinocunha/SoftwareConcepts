module Apps/WOPR/Restaurant1
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

// App specific views of the state of the concepts to simplify the specification and visualization

fun tables : set Table { R.available }
// Active reservations are those that have been reserved but not yet used
fun reservations : Client -> Table { R.reservations :> R.available }
fun reserved : set Table { L.labels.Reserved }

// The app invariant

// The tables labeled as Reserved are exactly those that are reserved by some client
check Invariant {
	always {
		no Reaction iff {
			reserved = Client.reservations
		}
	}
} for 2 Table, 2 Client, 8 Action, 3 Reaction expect 0

// Other properties

// Affix is only possible in reactions
check AffixOnlyInReactions {
	all t : Table | always {
		L.affix[t,Reserved] implies some Reaction
	}
} for 2 Table, 2 Client, 8 Action, 3 Reaction expect 0

// Detach is only possible in reactions
check DetachOnlyInReactions {
	all t : Table | always {
		L.detach[t,Reserved] implies some Reaction
	}
} for 2 Table, 2 Client, 8 Action, 3 Reaction expect 0

// Clear is only possible in reactions
check ClearOnlyInReactions {
	all t : Table | always {
		L.clear[t] implies some Reaction
	}
} for 2 Table, 2 Client, 8 Action, 3 Reaction expect 0

// Scenarios

// All tables are reserved and used by some client
// Then a reaction will add and later remove the reserved sign
run Scenario {
	eventually always no Reaction
	all t : Table | eventually R.use[Client,t]
} for exactly 1 Client, exactly 2 Table, 8 Action, 3 Reaction expect 1

// Reactions

/*
when
	R.reserve[c,t]
where
	t not in reserved
then
	L.affix[t,Reserved] or R.cancel[c,t] or R.use[c,t]
*/

var lone sig ReserveReaction extends Reaction { }

fact {
	always {
		some ReserveReaction iff {
			some c : Client, t : Table | before {
				not (L.affix[t,Reserved] or R.cancel[c,t] or R.use[c,t]) since (R.reserve[c,t] and t not in reserved)
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
	L.detach[t,Reserved] or L.clear[t] or some d : Client | R.reserve[d,t]
*/

var lone sig CancelReaction extends Reaction { }

fact {
	always {
		some CancelReaction iff {
			some c : Client, t : Table | before {
				not (L.detach[t,Reserved] or L.clear[t] or some d : Client | R.reserve[d,t]) since (R.cancel[c,t] and t in reserved)
			}
		}
	}
}

/*
when
	R.use[c,t]
where
	t in reserved
then
	L.detach[t,Reserved] or L.clear[t] or some d : Client | R.reserve[d,t]
*/

var lone sig UseReaction extends Reaction { }

fact {
	always {
		some UseReaction iff {
			some c : Client, t : Table | before {
				not (L.detach[t,Reserved] or L.clear[t] or some d : Client | R.reserve[d,t]) since (R.use[c,t] and t in reserved)
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
	t not in Client.reservations
*/

fact {
	all t : Table | always {
		L.clear[t] implies t not in Client.reservations
	}
}
