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

abstract sig TrashAction extends Action { } { concept in Trash }
sig Create extends TrashAction { item : Item }
fact {
	all x,y : Create | x.concept = y.concept and x.item = y.item implies x = y
}
sig Delete extends TrashAction { item : Item }
fact {
	all x,y : Delete | x.concept = y.concept and x.item = y.item implies x = y
}
sig Restore extends TrashAction { item : Item }
fact {
	all x,y : Restore | x.concept = y.concept and x.item = y.item implies x = y
}
sig Empty extends TrashAction {}
fact {
	all x,y : Empty | x.concept = y.concept implies x = y
}

pred create [c : Trash, i : Item] { 
	i not in c.(accessible+trashed)
	c.accessible' = c.accessible + i
	c.trashed' = c.trashed

	some a : Create & action | a.concept = c and a.item = i
}

pred delete [c : Trash, i : Item] {
	i in c.accessible
	c.accessible' = c.accessible - i
	c.trashed' = c.trashed + i

	some a : Delete & action | a.concept = c and a.item = i
}

pred restore [c : Trash, i : Item] {
	i in c.trashed
	c.accessible' = c.accessible + i
	c.trashed' = c.trashed - i

	some a : Restore & action | a.concept = c and a.item = i
}

pred empty [c : Trash] {
	some c.trashed
	no c.trashed'
	c.accessible' = c.accessible

	some a : Empty & action | a.concept = c
}

pred stutter [c : Trash] {
	c.accessible' = c.accessible
	c.trashed' = c.trashed

	no a : action | a.concept = c
}

fact Actions {
	all c : Trash | always { 
		(some i : Item | c.create[i]) or 
		(some i : Item | c.delete[i]) or 
		(some i : Item | c.restore[i]) or 
		c.empty[] or 
		c.stutter[]
	}
}

// Properties

// Items cannot be simultaneously accessible and trashed
check Invariant {
	always no Trash.accessible & Trash.trashed
} for 3 but exactly 1 Trash, 10 Action expect 0

// Expected value of accessible
check Accessible {
	all i : Item | always {
		i in Trash.accessible iff before {
			not Trash.delete[i] since (Trash.create[i] or Trash.restore[i])
		}
	}
} for 3 but exactly 1 Trash, 10 Action expect 0

// Expected value of trashed
check Trashed {
	all i : Item | always {
		i in Trash.trashed iff before {
			not (Trash.empty or Trash.restore[i]) since Trash.delete[i]
		}
	}
} for 3 but exactly 1 Trash, 10 Action expect 0

// If an item is deleted and then restored it will be accessible
check OP1 {
	all i : Item | always ((Trash.delete[i];Trash.restore[i]) implies i in Trash.accessible'')
} for 3 but exactly 1 Trash, 10 Action expect 0

// If an item is deleted and then the trash is emptied then the it is neither accessible nor trashed
check OP2 {
	all i : Item | always ((Trash.delete[i];Trash.empty[]) implies i not in Trash.(trashed+accessible)'')
} for 3 but exactly 1 Trash, 10 Action expect 0

// Scenarios

// All items are deleted and then the thrash is emptied
run Scenario1 {
	eventually (Item in Trash.trashed and Trash.empty[])
} for exactly 3 Item, exactly 1 Trash, 10 Action expect 1

// All items are deleted and then restored
run Scenario2 {
	always not Trash.empty[]
	eventually (Item in Trash.trashed and eventually Item in Trash.accessible )
} for exactly 2 Item, exactly 1 Trash, 10 Action expect 1
