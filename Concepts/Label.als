module Concepts/Label[Item,Tag]
open Action

// State

abstract sig Label extends Concept {
	var labels : Item -> Tag
}

// Initial state

fact Init {
	no labels
}

// Actions

var abstract sig LabelAction extends Action { var i : Item } { c in Label }

var sig Affix extends LabelAction { var t : Tag } {
	i->t not in c.labels
	labels' = labels + c->i->t
}

var sig Detach extends LabelAction { var t : Tag } {
	i->t in c.labels
	labels' = labels - c->i->t
}

var sig Clear extends LabelAction { } {
	some c.labels[i]
	labels' = labels - c->i->Tag
}

fact Stutter {
	always {
		no LabelAction implies labels' = labels
	}
}

pred affix [l : Label, x : Item, y : Tag] { some Affix and Affix.c = l and Affix.i = x and Affix.t = y }
pred detach [l : Label, x : Item, y : Tag] { some Detach and Detach.c = l and Detach.i = x and Detach.t = y }
pred clear [l : Label, x : Item] { some Clear and Clear.c = l and Clear.i = x }

// Properties

// If a label is affixed it remains in the item labels until detached or all labels of the item are cleared
check Principle {
	all i : Item, t : Tag | always (Label.affix[i,t] implies after ((Label.detach[i,t] or Label.clear[i]) releases t in Label.labels[i]))
} for 3 but 3 Action, exactly 1 Label expect 0

// Scenarios

// All labels affixed in one item and then cleared
run Scenario1 {
	eventually { Tag in Label.labels[Item] and Label.clear[Item] }
} for exactly 1 Item, exactly 3 Tag, 3 Action, exactly 1 Label expect 1

// All labels affixed in one item and then detached
run Scenario2 {
	eventually { Tag in Label.labels[Item] and ((some t : Tag | Label.detach[Item,t]) until no Label.labels[Item]) }
} for exactly 1 Item, exactly 3 Tag, 3 Action, exactly 1 Label expect 1
