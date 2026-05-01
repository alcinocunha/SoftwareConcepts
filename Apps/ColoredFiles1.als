module Apps/ColoredFiles1
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

// Only accessible files can have colors
check Design {
	always {
		no reactions iff {
			colors.Color in T.accessible
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// One file with all colors is deleted
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File.colors = Color and T.delete[File])
	eventually always no reactions
} for exactly 1 File, exactly 3 Color, 6 Action, 1 Reaction expect 1

// Reactions

/*
reaction delete_clear
when
	T.delete[f]
where
	some f.colors
then
	L.clear[f]
*/

sig Delete_Clear extends Reaction { file : File }
fact {
	all x,y : Delete_Clear | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some d : Delete_Clear & reactions_to_add | d.file = f) iff (T.delete[f] and some f.colors)
		(some d : Delete_Clear & reactions_to_remove | d.file = f) iff L.clear[f]
	}
}

/*
reaction affix_error
when
	L.affix[f,c]
where
	f not in T.accessible
then
	error
*/

sig Affix_Error extends Reaction { }
fact {
	all x,y : Affix_Error | x = y
}
fact {
	always {
		(some Affix_Error & reactions_to_add) iff (some f : File, c : Color | L.affix[f,c] and f not in T.accessible)
		(some Affix_Error & reactions_to_remove) iff error
	}
}
