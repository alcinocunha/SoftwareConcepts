module Concepts/Label[User,Item,Label]
open Action[User]

// State

one sig State {
	var labels_ : User -> Item -> Label
}

fun labels : User -> Item -> set Label { State.labels_ }

// Initial state

fact Init {
	no labels
}

// Actions

var abstract sig LabelAction extends Action { var i : Item }

var sig Affix extends LabelAction { var l : Label } {
	i->l not in u.labels
	labels' = labels + u->i->l
}

var sig Detach extends LabelAction { var l : Label } {
	i->l in u.labels
	labels' = labels - u->i->l
}

var sig Clear extends LabelAction { } {
	some u.labels[i]
	labels' = labels - u->i->Label
}

fact Stutter {
	always {
		no LabelAction implies labels' = labels
	}
}

pred affix [v : User, x : Item, y : Label] { some Affix and Affix.u = v and Affix.i = x and Affix.l = y }
pred detach [v : User, x : Item, y : Label] { some Detach and Detach.u = v and Detach.i = x and Detach.l = y }
pred clear [v : User, x : Item] { some Clear and Clear.u = v and Clear.i = x }

// Properties

// If a label is affixed it remains in the item labels until detached or all labels of the item are cleared
check Principle {
	all i : Item, l : Label | always (affix[User,i,l] implies after ((detach[User,i,l] or clear[User,i]) releases l in User.labels[i]))
} for 3 but 3 Action, exactly 1 User expect 0

// Scenarios

// All labels affixed in one item and then cleared
run Scenario1 {
	eventually { Label in User.labels[Item] and clear[User,Item] }
} for exactly 1 Item, exactly 3 Label, 3 Action, exactly 1 User expect 1

// All labels affixed in one item and then detached
run Scenario2 {
	eventually { Label in User.labels[Item] and ((some l : Label | detach[User,Item,l]) until no User.labels[Item]) }
} for exactly 1 Item, exactly 3 Label, 3 Action, exactly 1 User expect 1
