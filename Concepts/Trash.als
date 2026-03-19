module Trash[Item]
open Action

var sig accessible in Item {}
var sig trashed in Item {}

fact Init {
	no accessible
	no trashed
}

var abstract sig Trash extends Action {}

var sig Create extends Trash { var i : Item } { 
	i not in accessible+trashed
	accessible' = accessible + i
	trashed' = trashed
}

var sig Delete extends Trash { var i : Item } {
	i in accessible
	accessible' = accessible - i
	trashed' = trashed + i
}

var sig Restore extends Trash { var i : Item } {
	i in trashed
	accessible' = accessible + i
	trashed' = trashed - i
}

var sig Empty extends Trash {} {
	some trashed
	no trashed'
	accessible' = accessible
}

fact Stutter {
	always {
		no Trash implies {
			accessible' = accessible
			trashed' = trashed
		}
	}
}

pred create [x : Item] { some Create and Create.i = x }
pred delete [x : Item] { some Delete and Delete.i = x }
pred restore [x : Item] { some Restore and Restore.i = x }
pred empty { some Empty }

check Invariant {
	always no accessible & trashed
} for 3 but 4 Action

check Principle1 {
	all i : Item | always ((delete[i];restore[i]) implies i in accessible'')
} for 3 but 4 Action

check Principle2 {
	all i : Item | always ((delete[i];empty) implies i not in (trashed+accessible)'')
} for 3 but 4 Action

run Scenario1 {
	eventually (Item in trashed and empty)
} for exactly 3 Item, 4 Action expect 1

run Scenario2 {
	always not empty
	eventually (Item in trashed and eventually Item in accessible )
} for exactly 2 Item, 4 Action expect 1
