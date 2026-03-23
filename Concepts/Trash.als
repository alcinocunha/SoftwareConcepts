module Concepts/Trash[User,Item]
open Action[User]

// State

one sig State {
	var accessible_ : User -> Item,
	var trashed_ : User -> Item
}

fun accessible : User -> set Item { State.accessible_ }
fun trashed : User -> set Item { State.trashed_ }

// Initial state

fact Init {
	no accessible
	no trashed
}

// Actions

var abstract sig TrashAction extends Action {}

var sig Create extends TrashAction { var i : Item } { 
	i not in u.(accessible+trashed)
	accessible' = accessible + u->i
	trashed' = trashed
}

var sig Delete extends TrashAction { var i : Item } {
	i in u.accessible
	accessible' = accessible - u->i
	trashed' = trashed + u->i
}

var sig Restore extends TrashAction { var i : Item } {
	i in u.trashed
	accessible' = accessible + u->i
	trashed' = trashed - u->i
}

var sig Empty extends TrashAction { } {
	some u.trashed
	trashed' = trashed - u->Item
	accessible' = accessible
}

fact Stutter {
	always {
		no TrashAction implies {
			accessible' = accessible
			trashed' = trashed
		}
	}
}

pred create [a : User, x : Item] { some Create and Create.u = a and Create.i = x }
pred delete [a : User, x : Item] { some Delete and Delete.u = a and Delete.i = x }
pred restore [a : User, x : Item] { some Restore and Restore.u = a and Restore.i = x }
pred empty [a : User] { some Empty and Empty.u = a }

// Properties

// Items cannot be simultaneously accessible and trashed
check Invariant {
	always no User.accessible & User.trashed
} for 3 but 4 Action, exactly 1 User expect 0

// If an item is deleted and then restored it will be accessible
check Principle1 {
	all i : Item | always ((delete[User,i];restore[User,i]) implies i in User.accessible'')
} for 3 but 4 Action, exactly 1 User expect 0

// If an item is deleted and then the trash is emptied then the it is neither accessible nor trashed
check Principle2 {
	all i : Item | always ((delete[User,i];empty[User]) implies i not in User.(trashed+accessible)'')
} for 3 but 4 Action, exactly 1 User expect 0

// Scenarios

// All items are deleted and then the thrash is emptied
run Scenario1 {
	eventually (Item in User.trashed and empty[User])
} for exactly 3 Item, 4 Action, exactly 1 User expect 1

// All items are deleted and then restored
run Scenario2 {
	always not empty[User]
	eventually (Item in User.trashed and eventually Item in User.accessible )
} for exactly 2 Item, 4 Action, exactly 1 User expect 1
