module Action

abstract sig Concept {}
abstract sig User {}

var lone abstract sig Action { var c : Concept, var u : User }

