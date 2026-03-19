module Trash[Item]
open Action

// State

var sig accessible in Item {}
var sig trashed in Item {}

// Initial state

fact Init {
	no accessible
	no trashed
}

// Actions

var abstract sig TrashAction extends Action {}

var sig Create extends TrashAction { var i : Item } { 
	i not in accessible+trashed
	accessible' = accessible + i
	trashed' = trashed
}

var sig Delete extends TrashAction { var i : Item } {
	i in accessible
	accessible' = accessible - i
	trashed' = trashed + i
}

var sig Restore extends TrashAction { var i : Item } {
	i in trashed
	accessible' = accessible + i
	trashed' = trashed - i
}

var sig Empty extends TrashAction { } {
	some trashed
	no trashed'
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

pred create [x : Item] { some Create and Create.i = x }
pred delete [x : Item] { some Delete and Delete.i = x }
pred restore [x : Item] { some Restore and Restore.i = x }
pred empty { some Empty }

// Properties

// Items cannot be simultaneously accessible and trashed
check Invariant {
	always no accessible & trashed
} for 3 but 4 Action

// If an item is deleted and then restored it will be accessible
check Principle1 {
	all i : Item | always ((delete[i];restore[i]) implies i in accessible'')
} for 3 but 4 Action

// If an item is deleted and then the trash is emptied then the it is neither accessible nor trashed
check Principle2 {
	all i : Item | always ((delete[i];empty) implies i not in (trashed+accessible)'')
} for 3 but 4 Action

// Scenarios

// All items are deleted and then the thrash is emptied
run Scenario1 {
	eventually (Item in trashed and empty)
} for exactly 3 Item, 4 Action expect 1

// All items are deleted and then restored
run Scenario2 {
	always not empty
	eventually (Item in trashed and eventually Item in accessible )
} for exactly 2 Item, 4 Action expect 1
