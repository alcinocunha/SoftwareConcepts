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

// The design goal

// The tables labeled as Reserved are exactly those that are reserved by some client
check Design {
	always {
		no reactions iff {
			reserved = Client.reservations
		}
	}
} for 2 Table, 2 Client, 10 Action, 10 Reaction expect 0


// Scenarios

// All tables are reserved and used by some client
// Then a reaction will add and later remove the reserved sign
run Scenario {
	eventually always no reactions
	all t : Table | eventually R.use[Client,t]
} for exactly 1 Client, exactly 2 Table, 10 Action, 10 Reaction, 11 steps expect 1

// Reactions

/*
reaction reserve_affix
when
	R.reserve[c,t]
then
	L.affix[t,Reserved] 
*/

sig Reserve_Affix extends Reaction { table : Table }
fact {
	all x,y : Reserve_Affix | x.table = y.table implies x = y
}
fact {
	all t : Table | always {
		(some r : Reserve_Affix & reactions_to_add | r.table = t) iff (some c : Client | R.reserve[c,t])
		(some r : Reserve_Affix & reactions_to_remove | r.table = t) iff (L.affix[t,Reserved])
	}
}

/*
reaction cancel_detach
when
	R.cancel[c,t]
then
	L.detach[t,Reserved] or L.clear[t]
*/

sig Cancel_Detach extends Reaction { table : Table }
fact {
	all x,y : Cancel_Detach | x.table = y.table implies x = y
}
fact {
	all t : Table | always {
		(some r : Cancel_Detach & reactions_to_add | r.table = t) iff (some c : Client | R.cancel[c,t])
		(some r : Cancel_Detach & reactions_to_remove | r.table = t) iff (L.detach[t,Reserved] or L.clear[t])
	}
}	

/*
reaction use_detach
when
	R.use[c,t]
then
	L.detach[t,Reserved] or L.clear[t]
*/

sig Use_Detach extends Reaction { table : Table }
fact {
	all x,y : Use_Detach | x.table = y.table implies x = y
}
fact {
	all t : Table | always {
		(some r : Use_Detach & reactions_to_add | r.table = t) iff (some c : Client | R.use[c,t])
		(some r : Use_Detach & reactions_to_remove | r.table = t) iff (L.detach[t,Reserved] or L.clear[t])
	}
}

/*
reaction affix_error
when
	L.affix[t,Reserved]
where
	t not in Client.reservations
then
	error
*/

sig Affix_Error extends Reaction { }
fact {
	all x,y : Affix_Error | x = y
}
fact {
	always {
		(some Affix_Error & reactions_to_add) iff (some t : Table | L.affix[t,Reserved] and t not in Client.reservations)
		(some Affix_Error & reactions_to_remove) iff error
	}
}

/*
reaction detach_error
when
	L.detach[t,Reserved]
where
	t in Client.reservations
then
	error
*/

sig Detach_Error extends Reaction { }
fact {
	all x,y : Detach_Error | x = y
}
fact {
	always {
		(some Detach_Error & reactions_to_add) iff (some t : Table | L.detach[t,Reserved] and t in Client.reservations)
		(some Detach_Error & reactions_to_remove) iff error
	}
}

/*
reaction clear_error
when
	L.clear[t]
where
	t in Client.reservations
then
	error
*/

sig Clear_Error extends Reaction { }
fact {
	all x,y : Clear_Error | x = y
}
fact {
	always {
		(some Clear_Error & reactions_to_add) iff (some t : Table | L.clear[t] and t in Client.reservations)
		(some Clear_Error & reactions_to_remove) iff error
	}
}
