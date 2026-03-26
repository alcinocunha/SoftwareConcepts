module Apps/FileSystem1
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

// Single user with a single trash and labels

one sig U extends User {}
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

// Only accessible files can have colors
check Invariant {
	always {
		no Reaction iff colors.Color in accessible
	}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// One files with all colors is deleted
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File.colors = Color and T.delete[User,File])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 1 Reaction expect 1

// Reactions

/*
when
	T.delete[User,f]
where
	some f.colors
then
	L.clear[User,f] or T.restore[User,f]
*/

var lone sig DeleteClearOrRestore extends Reaction { }

fact {
	always {
		some DeleteClearOrRestore iff {
			some f : File | before (not (L.clear[User,f] or T.restore[User,f]) since (T.delete[User,f] and some f.colors))
		}
	}
}

// Preventions

/*
when
	L.affix[User,f,c]
require
	f in accessible
*/

fact {
	all f : File, c : Color | always {
		L.affix[User,f,c] implies f in accessible
	}
}

/*
when
	L.detach[User,f,c]
require
	f in accessible
*/

fact {
	all f : File, c : Color | always {
		L.detach[User,f,c] implies f in accessible
	}
}

/*
when
	T.create[User,f]
require
	no f.colors
*/

fact {
	all f : File | always {
		T.create[User,f] implies no f.colors
	}
}
