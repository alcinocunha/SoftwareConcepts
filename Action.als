module Action

abstract sig Concept {}

abstract sig Action {
	concept : one Concept
}

var lone sig action in Action {}