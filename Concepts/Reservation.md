# Reservation

## Specification

```
concept: Reservation[User,Resource]
purpose: To allow users to reserve resources for later use.
principle: If a user reserves a resource, then they can later use it, but if they cancel the reservation then they cannot use it.
state:
	reservations: User -> set Resource
	available: set Resource
actions:
	provide(r:Resource)
		requires: r is not in available
		effects: adds r to available and removes any previous reservations of r
	retract(r:Resource)
		requires: r is in available and is not in the reservations of any user
		effects: removes r from available
	reserve(u:User, r:Resource)
		requires: r is in available and is not in the reservations of any user
		effects: adds r to the reservations of u
	cancel(u:User, r:Resource)
		requires: r is in available and r is in the reservations of u
		effects: removes r from the reservations of u
	use(u:User, r:Resource)
		requires: r is in available and r is in the reservations of u
		effects: removes r from available
invariants: a resource can only be reserved by at most one user at a time
```

## Formalizations

* [Alloy](Reservation.als)
* [TLA+](Reservation.tla)