module Apps/ColoredFiles2
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

// The design goal

// Colors can be assigned to both accessible and trashed files
check Design {
	always {
		no reactions iff { 
			colors.Color in accessible+trashed
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// Two files with colors are deleted and the trash is emptied
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File in trashed and colors.Color = File and T.empty[])
	eventually always no reactions
} for exactly 2 File, exactly 3 Color, 10 Action, 10 Reaction expect 1

// Reactions

/*
reaction empty_clear
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f]
*/

sig Empty_Clear extends Reaction { file : File }
fact {
	all x,y : Empty_Clear | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some d : Empty_Clear & reactions_to_add | d.file = f) iff (T.empty[] and f in trashed and some f.colors)
		(some d : Empty_Clear & reactions_to_remove | d.file = f) iff L.clear[f]
	}
}

/*
reaction affix_error
when
	L.affix[f,c]
when
	f not in T.accessible and f not in T.trashed
then
	error
*/

sig Affix_Error extends Reaction { }
fact {
	all x,y : Affix_Error | x = y
}
fact {
	always {
		(some Affix_Error & reactions_to_add) iff (some f : File, c : Color | L.affix[f,c] and f not in T.accessible and f not in T.trashed)
		(some Affix_Error & reactions_to_remove) iff error
	}
}
