module Apps/WPR/FileSystem2
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

// Priority of reactions over requests

fact {
	PriorityToReactions
}


// The app invariant

// Colors can be assigned to both accessible and trashed files
check Invariant {
	always {
		no Reaction iff { 
			colors.Color in accessible+trashed
		}
	}
} for 2 but 7 Action, 3 Reaction expect 0

// Scenarios

// Two files with colors are deleted and the trash is emptied
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File in trashed and colors.Color = File and T.empty[])
	eventually always no Reaction
} for exactly 2 File, exactly 3 Color, 7 Action, 3 Reaction expect 1

// Reactions

/*
reaction EmptyClear[f : File]
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f]
*/

var sig EmptyClear extends Reaction { var f : File }
fact {
	always all r : EmptyClear {
		all d : EmptyClear' | d.f' = r.f implies d = r
	}
}
pred EmptyClear [x : File] { some d : EmptyClear | d.f = x }

fact {
	all f : File | always {
		EmptyClear[f] iff {
			before {
				not L.clear[f] since (T.empty[] and f in trashed and some f.colors)
			}
		}
	}
}

// Preventions

/*
when
	L.affix[f,c]
require
	f in accessible+trashed
*/

fact {
	all f : File, c : Color | always {
		L.affix[f,c] implies f in accessible+trashed
	}
}

