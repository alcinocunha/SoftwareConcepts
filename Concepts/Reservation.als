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

abstract sig ReservationAction extends Action { resource : Resource } { concept in Reservation }
sig Provide extends ReservationAction {}
fact {
	all x,y : Provide | x.concept = y.concept and x.resource = y.resource implies x = y
}
sig Retract extends ReservationAction {}
fact {
	all x,y : Retract | x.concept = y.concept and x.resource = y.resource implies x = y
}
sig Reserve extends ReservationAction { user : User }
fact {
	all x,y : Reserve | x.concept = y.concept and x.resource = y.resource and x.user = y.user implies x = y
}
sig Cancel extends ReservationAction { user : User }
fact {
	all x,y : Cancel | x.concept = y.concept and x.resource = y.resource and x.user = y.user implies x = y
}
sig Use extends ReservationAction { user : User }
fact {
	all x,y : Use | x.concept = y.concept and x.resource = y.resource and x.user = y.user implies x = y
}

pred provide [c : Reservation, r : Resource] {
	r not in c.available
	c.available' = c.available + r
	c.reservations' = c.reservations - User->r

	some a : Provide & action | a.concept = c and a.resource = r
}

pred retract [c : Reservation, r : Resource] {
	r in c.available
	r not in c.reservations[User]
	c.available' = c.available - r
	c.reservations' = c.reservations

	some a : Retract & action | a.concept = c and a.resource = r
}

pred reserve [c : Reservation, u : User, r : Resource] {
	r in c.available
	r not in c.reservations[User]
	c.available' = c.available
	c.reservations' = c.reservations + u->r

	some a : Reserve & action | a.concept = c and a.user = u and a.resource = r
}

pred cancel [c : Reservation, u : User, r : Resource] {
	r in c.available
	r in c.reservations[u]
	c.available' = c.available
	c.reservations' = c.reservations - u->r

	some a : Cancel & action | a.concept = c and a.user = u and a.resource = r
}

pred use [c : Reservation, u : User, r : Resource] {
	r in c.available
	r in c.reservations[u]
	c.available' = c.available - r
	c.reservations' = c.reservations

	some a : Use & action | a.concept = c and a.user = u and a.resource = r
}

pred stutter[c : Reservation] {
	c.available' = c.available
	c.reservations' = c.reservations

	no a : action | a.concept = c
}

fact Actions {
	all c : Reservation | always {
		(some r : Resource | c.provide[r]) or 
		(some r : Resource | c.retract[r]) or 
		(some u : User, r : Resource | c.reserve[u,r]) or 
		(some u : User, r : Resource | c.cancel[u,r]) or 
		(some u : User, r : Resource | c.use[u,r]) or 
		c.stutter[]
	}
}

// Properties

// Resources cannot but reserved and available
check Invariant {
	always {
		Reservation.reservations in User lone -> Resource
	}
} for 2 but 10 Action, exactly 1 Reservation expect 0

// A reserved resource was not retracted or reserved since it has been provided
check OP1 {
	all u : User, r : Resource | always {
		Reservation.reserve[u,r] implies before (not Reservation.retract[r] since Reservation.provide[r])
	}
} for 2 but 10 Action, exactly 1 Reservation expect 0

// A used resource was previously reserved and the reservation was not cancelled or used in the meantime
check OP2 {
	all u : User, r : Resource | always {
		Reservation.use[u,r] implies before (not (Reservation.cancel[u,r] or Reservation.use[u,r]) since Reservation.reserve[u,r])
	}
} for 2 but 10 Action, exactly 1 Reservation expect 0

// A reservation can only be cancelled if it was previously made and not cancelled or used in the meantime
check OP3 {
	all u : User, r : Resource | always {
		Reservation.cancel[u,r] implies before (not (Reservation.cancel[u,r] or Reservation.use[u,r]) since Reservation.reserve[u,r])
	}
} for 2 but 10 Action, exactly 1 Reservation expect 0

// Expected value of available
check Available {
	all r : Resource | always {
		r in Reservation.available iff before {
			not (Reservation.retract[r] or some u : User | Reservation.use[u,r]) since Reservation.provide[r]
		}
	}
} for 2 but 10 Action, exactly 1 Reservation expect 0

// Expected value of reservations
check Reservations {
	all u : User, r : Resource | always {
		u->r in Reservation.reservations iff before {
			not (Reservation.cancel[u,r] or Reservation.provide[r]) since Reservation.reserve[u,r]
		}
	}
} for 2 but 10 Action, exactly 1 Reservation expect 0

// Scenarios

// All resources are used by some user and the system returns to the initial state
run Scenario {
	some u : User | all r : Resource | eventually Reservation.use[u,r]
	eventually always (no available and no reservations)
} for exactly 2 User, exactly 2 Resource, 10 Action, exactly 1 Reservation, 12 steps expect 1
