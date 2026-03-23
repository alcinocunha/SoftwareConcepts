module Apps/Restaurant
open Action[User]
open Reaction

// Composed concepts

open Concepts/Reservation[User,Table]
open Concepts/Label[User,Table,Reserved]

// Multiple clients one restaurant

abstract sig User {}
sig Client extends User {}
one sig Restaurant extends User {}

// Types

sig Table {}
one sig Reserved {}

// The app invariant

// Reserved tables are labeled as Reserved
check Invariant {
	always {
		no Reaction iff {
			available in Restaurant -> Table
			reservations in Client -> Table
			labels in Restaurant -> Table -> Reserved
			Client.reservations = Restaurant.labels.Reserved
		}
	}
} for 2 Table, 2 Client, 9 Action, 3 Reaction expect 0

// Scenarios

// All tables are reserved and used by some client
// Then a reaction will add and later remove the reserved sign
run Scenario {
	eventually always no Reaction
	all t : Table | some c : Client | eventually use[c,t]
} for 1 Client, exactly 2 Table, 9 Action, 3 Reaction, 20 steps expect 1

// Reactions

/*
when
	reserve[c,t]
then
	affix[Restaurant,Reserved] or cancel[c,t]
*/

var lone sig ReserveAffixOrCancel extends Reaction { }

fact {
	always {
		some ReserveAffixOrCancel iff {
			some c : Client, t : Table | before {
				not (affix[Restaurant,t,Reserved] or cancel[c,t]) since reserve[c,t]
			}
		}
	}
}

/*
when
	cancel[c,t]
where
	Reserved in Restaurant.labels[t]
then
	dettach[Restaurant,t,Reserved]
*/

var lone sig CancelDetach extends Reaction { }

fact {
	always {
		some CancelDetach iff {
			some c : Client, t : Table | before {
				not detach[Restaurant,t,Reserved] since (cancel[c,t] and Reserved in Restaurant.labels[t])
			}
		}
	}
}

/*
when
	use[c,t]
then
	dettach[Restaurant,t,Reserved]
*/

var lone sig UseDetach extends Reaction { }

fact {
	always {
		some UseDetach iff {
			some c : Client, t : Table | before {
				not detach[Restaurant,t,Reserved] since use[c,t]
			}
		}
	}
}

// Preventions

/*
when
	affix[u,t,Reserved]
require
	u in Restaurant and t in User.reservations
*/

fact {
	all u : User, t : Table | always {
		affix[u,t,Reserved] implies u in Restaurant and t in Client.reservations
	}
}

/*
when
	detach[u,t,Reserved]
require
	u in Restaurant and t not in Client.reservations
*/

fact {
	all u : User, t : Table | always {
		detach[u,t,Reserved] implies u in Restaurant and t not in Client.reservations
	}
}

/*
when
	clear[u,t]
require
	false
*/

fact {
	all u : User, t : Table | always {
		clear[u,t] implies false
	}
}

/*
when
	provide[u,t]
require
	u in Restaurant
*/

fact {
	all u : User, t : Table | always {
		provide[u,t] implies u in Restaurant
	}
}

/*
when
	use[c,t]
require
	Reserved in Restaurant.labels[t]
*/

fact {
	all c : Client, t : Table | always {
		use[c,t] implies Reserved in Restaurant.labels[t]
	}
}

/*
when
	reserve[u,t]
require
	u in Client and Reserved not in Restaurant.labels[t]
*/

fact {
	all u : User, t : Table | always {
		reserve[u,t] implies u in Client and Reserved not in Restaurant.labels[t]
	}
}
