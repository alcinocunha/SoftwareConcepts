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

pred create [t : Trash, x : Item] { some Create and Create.c = t and Create.i = x }
pred delete [t : Trash, x : Item] { some Delete and Delete.c = t and Delete.i = x }
pred restore [t : Trash, x : Item] { some Restore and Restore.c = t and Restore.i = x }
pred empty [t : Trash] { some Empty and Empty.c = t }

// Properties

// Items cannot be simultaneously accessible and trashed
check Invariant {
	always no Trash.accessible & Trash.trashed
} for 3 but 4 Action, exactly 1 Trash expect 0

// Expected value of accessible
check Accessible {
	all i : Item | always {
		i in Trash.accessible iff before {
			not Trash.delete[i] since (Trash.create[i] or Trash.restore[i])
		}
	}
} for 3 but 4 Action, exactly 1 Trash expect 0

// Expected value of trashed
check Trashed {
	all i : Item | always {
		i in Trash.trashed iff before {
			not (Trash.empty or Trash.restore[i]) since Trash.delete[i]
		}
	}
} for 3 but 4 Action, exactly 1 Trash expect 0

// If an item is deleted and then restored it will be accessible
check Principle1 {
	all i : Item | always ((Trash.delete[i];Trash.restore[i]) implies i in Trash.accessible'')
} for 3 but 4 Action, exactly 1 Trash expect 0

// If an item is deleted and then the trash is emptied then the it is neither accessible nor trashed
check Principle2 {
	all i : Item | always ((Trash.delete[i];Trash.empty[]) implies i not in Trash.(trashed+accessible)'')
} for 3 but 4 Action, exactly 1 Trash expect 0

// Scenarios

// All items are deleted and then the thrash is emptied
run Scenario1 {
	eventually (Item in Trash.trashed and Trash.empty[])
} for exactly 3 Item, 4 Action, exactly 1 Trash expect 1

// All items are deleted and then restored
run Scenario2 {
	always not Trash.empty[]
	eventually (Item in Trash.trashed and eventually Item in Trash.accessible )
} for exactly 2 Item, 4 Action, exactly 1 Trash expect 1
