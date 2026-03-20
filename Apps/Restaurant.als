module Apps/Restaurant

// Composed concepts

open Concepts/Reservation[Client,Table]
open Concepts/Label[Table,Reserved]

sig Client {}
sig Table {}
one sig Reserved {}

// The app invariant

// Reserved tables are labeled as Reserved
check Invariant {
	always {
		not syncing iff {
			Client.reservations = labels.Reserved
		}
	}
} for 2 but 9 Action

// Scenarios

// All tables are reserved and used by some client
// Syncronization will add and later removed the reserved label 
run Scenario {
	eventually always not syncing
	all t : Table | some c : Client | eventually use[c,t]
} for 1 Client, exactly 2 Table, 9 Action, 20 steps

// When is the app syncing

pred syncing {
	sync_reserve or sync_cancel or sync_use
}

// For visualization only
one sig Syncing {}
fun syncing : Syncing { { s : Syncing | syncing } }

// Synchronzation rules

/*
when
	affix[t,Reserved]
require
	t in User.reservations
*/

fact {
	all t : Table | always {
		affix[t,Reserved] implies t in Client.reservations
	}
}

/*
when
	reserve[c,t]
then
	affix[t,Reserved] or cancel[c,t]
*/

pred sync_reserve {
	some c : Client, t : Table | before {
		not (affix[t,Reserved] or cancel[c,t]) since reserve[c,t]
	}
}

/*
when
	use[c,t]
require
	Reserved in t.labels
*/

fact {
	all c : Client, t : Table | always {
		use[c,t] implies Reserved in t.labels
	}
}

/*
when
	detach[t,Reserved]
require
	t not in Client.reservations
*/

fact {
	all t : Table | always {
		detach[t,Reserved] implies t not in Client.reservations
	}
}

/*
when
	clear[t]
require
	false
*/

fact {
	all t : Table | always {
		clear[t] implies false
	}
}

/*
when
	cancel[c,t]
where
	Reserved in t.labels
then
	dettach[t,Reserved]
*/

pred sync_cancel {
	some c : Client, t : Table | before {
		not detach[t,Reserved] since (cancel[c,t] and Reserved in t.labels)
	}
}

/*
when
	use[c,t]
then
	dettach[t,Reserved]
*/

pred sync_use {
	some c : Client, t : Table | before {
		not detach[t,Reserved] since use[c,t]
	}
}

/*
when
	reserve[c,t]
require
	Reserved not in t.labels
*/

fact {
	all c : Client, t : Table | always {
		reserve[c,t] implies Reserved not in t.labels
	}
}
