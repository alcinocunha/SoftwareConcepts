module Action

abstract sig User {}

var lone abstract sig Action { var u : User }

pred false {
	some none
}
