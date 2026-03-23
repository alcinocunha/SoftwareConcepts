module Concepts/Label[User,Item,Tag]
open Action[User]

// State

one sig Label {
	var labels_ : User -> Item -> Tag
}

fun labels : User -> Item -> set Tag { Label.labels_ }

// Initial state

fact Init {
	no labels
}

// Actions

var abstract sig LabelAction extends Action { var i : Item }

var sig Affix extends LabelAction { var t : Tag } {
	i->t not in u.labels
	labels' = labels + u->i->t
}

var sig Detach extends LabelAction { var t : Tag } {
	i->t in u.labels
	labels' = labels - u->i->t
}

var sig Clear extends LabelAction { } {
	some u.labels[i]
	labels' = labels - u->i->Tag
}

fact Stutter {
	always {
		no LabelAction implies labels' = labels
	}
}

pred affix [v : User, x : Item, y : Tag] { some Affix and Affix.u = v and Affix.i = x and Affix.t = y }
pred detach [v : User, x : Item, y : Tag] { some Detach and Detach.u = v and Detach.i = x and Detach.t = y }
pred clear [v : User, x : Item] { some Clear and Clear.u = v and Clear.i = x }

// Properties

// If a tag is affixed it remains in the item labels until detached or all tags of the item are cleared
check Principle {
	all i : Item, t : Tag | always (affix[User,i,t] implies after ((detach[User,i,t] or clear[User,i]) releases t in User.labels[i]))
} for 3 but 3 Action, exactly 1 User expect 0

// Scenarios

// All tags affixed in one item and then cleared
run Scenario1 {
	eventually { Tag in User.labels[Item] and clear[User,Item] }
} for exactly 1 Item, exactly 3 Tag, 3 Action, exactly 1 User expect 1

// All tags affixed in one item and then detached
run Scenario2 {
	eventually { Tag in User.labels[Item] and ((some t : Tag | detach[User,Item,t]) until no User.labels[Item]) }
} for exactly 1 Item, exactly 3 Tag, 3 Action, exactly 1 User expect 1
