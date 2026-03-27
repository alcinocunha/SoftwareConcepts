module Concepts/Reservation[User,Resource]
open Action

// State

abstract sig Reservation extends Concept {
	var available : set Resource,
	var reservations : User -> Resource
}

// Initial state

fact Init {
	no available
	no reservations
}

// Actions

var abstract sig ReservationAction extends Action { var u : User,var r : Resource } { c in Reservation }

var sig Provide extends ReservationAction { } {
	r not in c.available
	available' = available + c->r
	reservations' = reservations
}

var sig Retract extends ReservationAction { } {
	r in c.available
	r not in c.reservations[User]
	available' = available - c->r
	reservations' = reservations
}

var sig Reserve extends ReservationAction { } {
	r in c.available
	r not in c.reservations[User]
	available' = available
	reservations' = reservations + c->u->r
}

var sig Cancel extends ReservationAction { } {
	r in c.reservations[u]
	available' = available
	reservations' = reservations - c->u->r	
}

var sig Use extends ReservationAction { } {
	r in c.reservations[u]
	available' = available
	reservations' = reservations - c->u->r	
}

fact Stutter {
	always {
		no ReservationAction implies {
			available' = available
			reservations' = reservations
		}
	}
}

pred provide [ s : Reservation, v : User, x : Resource ] { some Provide and Provide.c = s and Provide.u = v and Provide.r = x }
pred retract [ s : Reservation, v : User, x : Resource ] { some Retract and Retract.c = s and Retract.u = v and Retract.r = x }
pred reserve [ s : Reservation, v : User, x : Resource ] { some Reserve and Reserve.c = s and Reserve.u = v and Reserve.r = x }
pred cancel [ s : Reservation, v : User, x : Resource ] { some Cancel and Cancel.c = s and Cancel.u = v and Cancel.r = x }
pred use [ s : Reservation, v : User, x : Resource ] { some Use and Use.c = s and Use.u = v and Use.r = x }

// Properties

// Resources cannot but reserved and available
check Invariant {
	always {
		Reservation.reservations[User] in Reservation.available
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// A reserved resource was not retracted since it has been provided
check Principle1 {
	all u : User, r : Resource | always {
		Reservation.reserve[u,r] implies before some v : User | (not Reservation.retract[v,r] since Reservation.provide[v,r])
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// A used resource was previously reserved and the reservation was not cancelled in the meantime
check Principle2 {
	all u : User, r : Resource | always {
		Reservation.use[u,r] implies before (not Reservation.cancel[u,r] since Reservation.reserve[u,r])
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// Scenarios

// All resources are used by some user and then retracted
run Scenario {
	some u : User | all r : Resource | eventually Reservation.use[u,r]
	eventually always no Reservation.available
} for exactly 2 User, exactly 2 Resource, 5 Action, exactly 1 Reservation expect 1
