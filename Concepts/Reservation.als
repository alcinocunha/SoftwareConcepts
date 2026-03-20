module Reservation[User,Resource]
open Action

// State

var sig available in Resource {}
sig User_ in User {
	var reservations : set Resource
}
fact { User_ = User }

// Initial state

fact Init {
	no available
	no reservations
}

// Actions

var abstract sig ReservationAction extends Action { var r : Resource }

var sig Provide extends ReservationAction { } {
	r not in available + User.reservations
	available' = available + r
	reservations' = reservations
}

var sig Retract extends ReservationAction { } {
	r in available
	available' = available - r
	reservations' = reservations
}

var sig Reserve extends ReservationAction { var u : User } {
	r in available
	available' = available - r
	reservations' = reservations + u->r
}

var sig Cancel extends ReservationAction { var u : User } {
	r in u.reservations
	available' = available + r
	reservations' = reservations - u->r	
}

var sig Use extends ReservationAction { var u : User } {
	r in u.reservations
	available' = available + r
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

pred provide [ x : Resource ] { some Provide and Provide.r = x }
pred retract [ x : Resource ] { some Retract and Retract.r = x }
pred reserve [ x : User, y : Resource ] { some Reserve and Reserve.u = x and Reserve.r = y }
pred cancel [ x : User, y : Resource ] { some Cancel and Cancel.u = x and Cancel.r = y }
pred use [ x : User, y : Resource ] { some Use and Use.u = x and Use.r = y }

// Properties

// Resources cannot but reserved and available
check Invariant {
	always {
		no User.reservations & available
	}
} for 3 but 5 Action

// A reserved resource was not retracted since it has been provided
check Principle1 {
	all u : User, r : Resource | always {
		reserve[u,r] implies before (not retract[r] since provide[r])
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
	all r : Resource | some u : User | eventually use[u,r]
	eventually always no available + User.reservations
} for 1 User, exactly 2 Resource, 5 Action
