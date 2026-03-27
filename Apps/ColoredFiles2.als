module Apps/FileSystem2
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

// App specific relations

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }
fun colors : File -> set Color { L.labels }

// The app invariant

// Colors can be assigned to both accessible and trashed files
check Invariant {
	always {
		no Reaction iff colors.Color in accessible+trashed
	}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// Two files with colors are deleted and the trash is emptied
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File in trashed and colors.Color = File and T.empty[])
	eventually always no Reaction
} for exactly 2 File, exactly 3 Color, 7 Action, 1 Reaction expect 1

// Reactions

/*
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f]
*/

var lone sig EmptyClear extends Reaction { }

fact {
	always {
		some EmptyClear iff {
			some f : File | before {
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

/*
when
	L.detach[f,c]
require
	f in accessible+trashed
*/

fact {
	all f : File, c : Color | always {
		L.detach[f,c] implies f in accessible+trashed
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

