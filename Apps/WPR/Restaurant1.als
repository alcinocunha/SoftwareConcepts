module Apps/Restaurant1
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

// Priority of reactions over requests

fact {
	PriorityToReactions
}

// The app invariant

// The tables labeled as Reserved are exactly those that are reserved by some client
check Invariant {
	always {
		no Reaction iff {
			reserved = Client.reservations
		}
	}
} for 2 Table, 2 Client, 8 Action, 4 Reaction expect 0

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
} for exactly 1 Client, exactly 2 Table, 8 Action, 4 Reaction, 11 steps expect 1

// Reactions

/*
reaction ReserveAffix[t : Table]
when
	R.reserve[c,t]
then
	L.affix[t,Reserved] 
*/

var sig ReserveAffix extends Reaction { var t : Table }
fact {	
	always all r : ReserveAffix {
		all d : ReserveAffix' | d.t' = r.t implies d = r
	}
}
pred ReserveAffix [x : Table] { some d : ReserveAffix | d.t = x }

fact {
	all t : Table | always {
		ReserveAffix[t] iff {
			some c : Client | before {
				not L.affix[t,Reserved] since R.reserve[c,t]
			}
		}
	}
}

/*
reaction CancelDetach[t : Table]
when
	R.cancel[c,t]
then
	L.detach[t,Reserved] or L.clear[t]
*/

var sig CancelDetach extends Reaction { var t : Table }
fact {
	always all r : CancelDetach {
		all d : CancelDetach' | d.t' = r.t implies d = r
	}
}
pred CancelDetach [x : Table] { some d : CancelDetach | d.t = x }

fact {
	all t : Table | always {
		CancelDetach[t] iff {
			some c : Client | before {
				not (L.detach[t,Reserved] or L.clear[t]) since R.cancel[c,t]
			}
		}
	}
}

/*
reaction UseDetach[t : Table]
when
	R.use[c,t]
then
	L.detach[t,Reserved] or L.clear[t]
*/

var sig UseDetach extends Reaction { var t : Table }
fact {
	always all r : UseDetach {
		all d : UseDetach' | d.t' = r.t implies d = r
	}
}
pred UseDetach [x : Table] { some d : UseDetach | d.t = x }

fact {
	all t : Table | always {
		UseDetach[t] iff {
			some c : Client | before {
				not (L.detach[t,Reserved] or L.clear[t]) since R.use[c,t]
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
