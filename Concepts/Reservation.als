module Concepts/Reservation[User,Resource]
open Action[User]

// State

one sig Reservation {
	var available_ : User -> set Resource,
	var reservations_ : User -> set Resource
}

fun available : User -> set Resource { Reservation.available_ }
fun reservations : User -> set Resource { Reservation.reservations_ }

// Initial state

fact Init {
	no available
	no reservations
}

// Actions

var abstract sig ReservationAction extends Action { var r : Resource }

var sig Provide extends ReservationAction { } {
	r not in User.available
	available' = available + u->r
	reservations' = reservations
}

var sig Retract extends ReservationAction { } {
	r in u.available
	r not in User.reservations
	available' = available - u->r
	reservations' = reservations
}

var sig Reserve extends ReservationAction { } {
	r in User.available
	r not in User.reservations
	available' = available
	reservations' = reservations + u->r
}

var sig Cancel extends ReservationAction { } {
	r in u.reservations
	available' = available
	reservations' = reservations - u->r	
}

var sig Use extends ReservationAction { } {
	r in u.reservations
	available' = available
	reservations' = reservations - u->r	
}

fact Stutter {
	always {
		no ReservationAction implies {
			available' = available
			reservations' = reservations
		}
	}
}

pred provide [ v : User, x : Resource ] { some Provide and Provide.u = v and Provide.r = x }
pred retract [ v : User, x : Resource ] { some Retract and Retract.u = v and Retract.r = x }
pred reserve [ v : User, x : Resource ] { some Reserve and Reserve.u = v and Reserve.r = x }
pred cancel [ v : User, x : Resource ] { some Cancel and Cancel.u = v and Cancel.r = x }
pred use [ v : User, x : Resource ] { some Use and Use.u = v and Use.r = x }

// Properties

// Resources cannot but reserved and available
check Invariant {
	always {
		User.reservations in User.available
		all r : Resource | lone available.r and lone reservations.r
	}
} for 2 but 5 Action

// A reserved resource was not retracted since it has been provided
check Principle1 {
	all u : User, r : Resource | always {
		reserve[u,r] implies before some v : User | (not retract[v,r] since provide[v,r])
	}
} for 2 but 5 Action

// A used resource was previously reserved and the reservation was not cancelled in the meantime
check Principle2 {
	all u : User, r : Resource | always {
		use[u,r] implies before (not cancel[u,r] since reserve[u,r])
	}
} for 2 but 5 Action

// Scenarios

// All resources are used by some user and then retracted
run Scenario {
	some u : User | all r : Resource | eventually use[u,r]
	eventually always no available
} for exactly 2 User, exactly 2 Resource, 5 Action
