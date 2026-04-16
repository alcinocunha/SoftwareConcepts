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

var abstract sig ReservationAction extends Action { var r : Resource } { c in Reservation }

var sig Provide extends ReservationAction { } {
	r not in c.available
	available' = available + c->r
	reservations' = reservations - c->User->r
}

var sig Retract extends ReservationAction { } {
	r in c.available
	r not in c.reservations[User]
	available' = available - c->r
	reservations' = reservations
}

var sig Reserve extends ReservationAction { var u : User } {
	r in c.available
	r not in c.reservations[User]
	available' = available
	reservations' = reservations + c->u->r
}

var sig Cancel extends ReservationAction { var u : User } {
	r in c.available
	r in c.reservations[u]
	available' = available
	reservations' = reservations - c->u->r	
}

var sig Use extends ReservationAction { var u : User } {
	r in c.available
	r in c.reservations[u]
	available' = available - c->r
	reservations' = reservations
}

fact Stutter {
	always {
		no ReservationAction implies {
			available' = available
			reservations' = reservations
		}
	}
}

pred provide [ s : Reservation, x : Resource ] { some Provide and Provide.c = s and Provide.r = x }
pred retract [ s : Reservation, x : Resource ] { some Retract and Retract.c = s and Retract.r = x }
pred reserve [ s : Reservation, v : User, x : Resource ] { some Reserve and Reserve.c = s and Reserve.u = v and Reserve.r = x }
pred cancel [ s : Reservation, v : User, x : Resource ] { some Cancel and Cancel.c = s and Cancel.u = v and Cancel.r = x }
pred use [ s : Reservation, v : User, x : Resource ] { some Use and Use.c = s and Use.u = v and Use.r = x }

// Properties

// Resources cannot but reserved and available
check Invariant {
	always {
		Reservation.reservations in User lone -> Resource
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// A reserved resource was not retracted or reserved since it has been provided
check OP1 {
	all u : User, r : Resource | always {
		Reservation.reserve[u,r] implies before (not Reservation.retract[r] since Reservation.provide[r])
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// A used resource was previously reserved and the reservation was not cancelled or used in the meantime
check OP2 {
	all u : User, r : Resource | always {
		Reservation.use[u,r] implies before (not (Reservation.cancel[u,r] or Reservation.use[u,r]) since Reservation.reserve[u,r])
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// A reservation can only be cancelled if it was previously made and not cancelled or used in the meantime
check OP3 {
	all u : User, r : Resource | always {
		Reservation.cancel[u,r] implies before (not (Reservation.cancel[u,r] or Reservation.use[u,r]) since Reservation.reserve[u,r])
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// Expected value of available
check Available {
	all r : Resource | always {
		r in Reservation.available iff before {
			not (Reservation.retract[r] or some u : User | Reservation.use[u,r]) since Reservation.provide[r]
		}
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// Expected value of reservations
check Reservations {
	all u : User, r : Resource | always {
		u->r in Reservation.reservations iff before {
			not (Reservation.cancel[u,r] or Reservation.provide[r]) since Reservation.reserve[u,r]
		}
	}
} for 2 but 5 Action, exactly 1 Reservation expect 0

// Scenarios

// All resources are used by some user and then retracted
run Scenario {
	some u : User | all r : Resource | eventually Reservation.use[u,r]
	eventually always no Reservation.available
} for exactly 2 User, exactly 2 Resource, 5 Action, exactly 4 Reservation expect 1
