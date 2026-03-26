module Concepts/Trash[Item]
open Action

// State

abstract sig Trash extends Concept {
	var accessible : set Item,
	var trashed : set Item
}

// Initial state

fact Init {
	no accessible
	no trashed
}

// Actions

var abstract sig TrashAction extends Action {} { c in Trash }

var sig Create extends TrashAction { var i : Item } { 
	i not in c.(accessible+trashed)
	accessible' = accessible + c->i
	trashed' = trashed
}

var sig Delete extends TrashAction { var i : Item } {
	i in c.accessible
	accessible' = accessible - c->i
	trashed' = trashed + c->i
}

var sig Restore extends TrashAction { var i : Item } {
	i in c.trashed
	accessible' = accessible + c->i
	trashed' = trashed - c->i
}

var sig Empty extends TrashAction { } {
	some c.trashed
	trashed' = trashed - c->Item
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

pred create [t : Trash, a : User, x : Item] { some Create and Create.c = t and Create.u = a and Create.i = x }
pred delete [t : Trash, a : User, x : Item] { some Delete and Delete.c = t and Delete.u = a and Delete.i = x }
pred restore [t : Trash, a : User, x : Item] { some Restore and Restore.c = t and Restore.u = a and Restore.i = x }
pred empty [t : Trash, a : User] { some Empty and Empty.c = t and Empty.u = a }

// Properties

// Items cannot be simultaneously accessible and trashed
check Invariant {
	always no Trash.accessible & Trash.trashed
} for 3 but 4 Action, exactly 1 Trash expect 0

// If an item is deleted and then restored it will be accessible
check Principle1 {
	all i : Item, u,v : User | always ((Trash.delete[u,i];Trash.restore[v,i]) implies i in Trash.accessible'')
} for 3 but 4 Action, exactly 1 Trash expect 0

// If an item is deleted and then the trash is emptied then the it is neither accessible nor trashed
check Principle2 {
	all i : Item, u,v : User | always ((Trash.delete[u,i];Trash.empty[v]) implies i not in Trash.(trashed+accessible)'')
} for 3 but 4 Action, exactly 1 Trash expect 0

// Scenarios

// All items are deleted and then the thrash is emptied
run Scenario1 {
	eventually (Item in Trash.trashed and Trash.empty[User])
} for exactly 3 Item, 4 Action, exactly 1 User, exactly 1 Trash expect 1

// All items are deleted and then restored
run Scenario2 {
	always not Trash.empty[User]
	eventually (Item in Trash.trashed and eventually Item in Trash.accessible )
} for exactly 2 Item, 4 Action, exactly 1 User, exactly 1 Trash expect 1
