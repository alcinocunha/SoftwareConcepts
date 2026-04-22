module Apps/WPR/ColoredFiles1
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

// This app does not assume reactions have priority over requests

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
} for exactly 1 File, exactly 3 Color, 10 Action, 10 Reaction expect 1

// Reactions


/*
reaction delete_with_colors
when
	T.delete[f]
where
	some f.colors
then
	L.clear[f] or (one f.colors and L.detach[f,c]) or T.restore[f] or T.empty[]
*/

sig Delete_With_Colors extends Reaction { file : File }
fact {
	all x,y : Delete_With_Colors | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some d : Delete_With_Colors & reactions_to_add | d.file = f) iff (T.delete[f] and some f.colors)
		(some d : Delete_With_Colors & reactions_to_remove | d.file = f) iff (L.clear[f] or (one f.colors and L.detach[f, f.colors]) or T.restore[f] or T.empty[])
	}
}

/*
reaction affix_not_accessible
when
	L.affix[f,c]
where
	f not in T.accessible
then
	L.detach[f,c] or T.restore[f] or L.clear[f] or T.create[f]
*/

sig Affix_Not_Accessible extends Reaction { file : File, color : Color }
fact {
	all x,y : Affix_Not_Accessible | x.file = y.file and x.color = y.color implies x = y
}
fact {
	all f : File, c : Color | always{
		(some a : Affix_Not_Accessible & reactions_to_add | a.file = f and a.color = c) iff (L.affix[f,c] and f not in T.accessible)
		(some a : Affix_Not_Accessible & reactions_to_remove | a.file = f and a.color = c) iff (L.detach[f,c] or T.restore[f] or L.clear[f] or T.create[f])
	}
}

/*
reaction empty_with_colors
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f] or (one f.colors and L.detach[f,f.colors]) or T.create[f]
*/

sig Empty_With_Colors extends Reaction { file : File }
fact {
	all x,y : Empty_With_Colors | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some e : Empty_With_Colors & reactions_to_add | e.file = f) iff (T.empty[] and f in trashed and some f.colors)
		(some e : Empty_With_Colors & reactions_to_remove | e.file = f) iff (L.clear[f] or (one f.colors and L.detach[f,f.colors]) or T.create[f])
	}
}
