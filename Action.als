module Action

abstract sig Action {
	concept : one Concept
}

var lone sig occurred in Action {}

fact { no occurred }

fun action : set Action { occurred' }

abstract sig Concept {}

