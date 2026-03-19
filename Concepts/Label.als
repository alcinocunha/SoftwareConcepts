module Label[Item,Tag]
open Action

// State

sig Item_ in Item { // hack to add relation to parameter signature
	var labels : set Tag
}
fact { Item_ = Item }

// Initial state

fact Init {
	no labels
}

// Actions

var abstract sig LabelAction extends Action { var i : Item }

var sig Affix extends LabelAction { var l : Tag } {
	i->l not in labels
	labels' = labels + i->l
}

var sig Detach extends LabelAction { var l : Tag } {
	i->l in labels
	labels' = labels - i->l
}

var sig Clear extends LabelAction { } {
	some i.labels
	labels' = labels - i->Tag
}

fact Stutter {
	always {
		no LabelAction implies labels' = labels
	}
}

pred affix [x : Item, y : Tag] { some Affix and Affix.i = x and Affix.l = y }
pred detach [x : Item, y : Tag] { some Detach and Detach.i = x and Detach.l = y }
pred clear [x : Item] { some Clear and Clear.i = x }

// Properties

// If a tag is affixed it remains in the item labels until detached or all tags of the item are cleared
check Principle {
	all i : Item, l : Tag | always (affix[i,l] implies after ((detach[i,l] or clear[i]) releases l in i.labels))
} for 3 but 3 Action

// Scenarios

// All tags affixed in one item and then cleared
run Scenario1 {
	eventually { Tag in Item.labels and clear[Item] }
} for exactly 1 Item, exactly 3 Tag, 3 Action

// All tags affixed in one item and then detached
run Scenario2 {
	eventually { Tag in Item.labels and ((some l : Tag | detach[Item,l]) until no Item.labels) }
} for exactly 1 Item, exactly 3 Tag, 3 Action
