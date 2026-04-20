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

abstract sig LabelAction extends Action { item : Item } { concept in Label }
sig Affix extends LabelAction { label : Tag }
fact {
	all x,y : Affix | x.concept = y.concept and x.item = y.item and x.label = y.label implies x = y
}
sig Detach extends LabelAction { label : Tag }
fact {
	all x,y : Detach | x.concept = y.concept and x.item = y.item and x.label = y.label implies x = y
}
sig Clear extends LabelAction {}
fact {
	all x,y : Clear | x.concept = y.concept and x.item = y.item implies x = y
}

pred affix [c : Label, i : Item, t : Tag] {
	i->t not in c.labels
	labels' = labels + c->i->t

	some a : Affix | a.concept = c and a.item = i and a.label = t and occurred' = a
}
pred detach [c : Label, i : Item, t : Tag] {
	i->t in c.labels
	labels' = labels - c->i->t

	some a : Detach | a.concept = c and a.item = i and a.label = t and occurred' = a
}

pred clear [c : Label, i : Item] {
	some c.labels[i]
	labels' = labels - c->i->Tag

	some a : Clear | a.concept = c and a.item = i and occurred' = a
}

pred stutter {
	labels' = labels

	no occurred' & LabelAction
}

fact Actions {
	always {
		(some c : Label, i : Item, t : Tag | affix[c,i,t]) or
		(some c : Label, i : Item, t : Tag | detach[c,i,t]) or
		(some c : Label, i : Item | clear[c,i]) or
		stutter
	}
}

// Properties

// If a label is affixed it remains in the item labels until detached or all labels of the item are cleared
check Principle {
	all i : Item, t : Tag | always (Label.affix[i,t] implies after ((Label.detach[i,t] or Label.clear[i]) releases t in Label.labels[i]))
} for 3 but 10 Action, exactly 1 Label expect 0

// Scenarios

// All labels affixed in one item and then cleared
run Scenario1 {
	eventually { Tag in Label.labels[Item] and Label.clear[Item] }
} for exactly 1 Item, exactly 3 Tag, 10 Action, exactly 1 Label expect 1

// All labels affixed in one item and then detached
run Scenario2 {
	eventually { Tag in Label.labels[Item] and ((some t : Tag | Label.detach[Item,t]) until no Label.labels[Item]) }
} for exactly 1 Item, exactly 3 Tag, 10 Action, exactly 1 Label expect 1
