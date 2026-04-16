module Apps/WOPR/FileSystem1
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

// One trash with labels

one sig T extends Trash {}
one sig L extends Label {}

// Types

sig File {}
sig Color {}

// Projections of the state of the concepts to simplify the specification and visualization

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }
fun colors : File -> set Color { L.labels }

// The app invariant

// Only accessible files can have colors
check Invariant {
	always {
		no Reaction iff colors.Color in accessible
	}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// One file with all colors is deleted
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File.colors = Color and T.delete[File])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 1 Reaction expect 1

// Reactions

/*
when
	T.delete[f]
where
	some f.colors
then
	L.clear[f] or T.restore[f]
*/

var lone sig DeleteClearOrRestore extends Reaction { }

fact {
	always {
		some DeleteClearOrRestore iff {
			some f : File | before (not (L.clear[f] or T.restore[f]) since (T.delete[f] and some f.colors))
		}
	}
}

// Preventions

/*
when
	L.affix[f,c]
require
	f in accessible
*/

fact {
	all f : File, c : Color | always {
		L.affix[f,c] implies f in accessible
	}
}

/*
when
	L.detach[f,c]
require
	f in accessible
*/

fact {
	all f : File, c : Color | always {
		L.detach[f,c] implies f in accessible
	}
}

/*
when
	T.create[f]
require
	no f.colors
*/

fact {
	all f : File | always {
		T.create[f] implies no f.colors
	}
}
