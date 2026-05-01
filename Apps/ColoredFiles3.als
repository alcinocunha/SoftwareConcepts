module Apps/ColoredFiles3
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
one sig Red extends Color {}

// Projections of the state of the concepts to simplify the specification and visualization

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }
fun colors : File -> set Color { L.labels }

// The design goal

// Colors can be assigned to both accessible and trashed files
// and trashed files have the red color
check Design {
	always {
		no reactions iff {
			colors.Color in accessible+trashed
			colors.Red = trashed
		}
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// One file will all possible colors is deleted and later the trash is emptied
// Reactions will affix the red color to the trashed file and then clear all its colors
run Scenario1 {
	eventually {
		File.colors = Color-Red and T.delete[File]
		eventually T.empty[]
	}
	eventually always no reactions
} for exactly 1 File, exactly 3 Color, 10 Action, 10 Reaction expect 1

// One file will all possible colors is deleted and later restored
// Reactions will affix the red color to the trashed file and then remove the red color
run Scenario2 {
	eventually {
		File.colors = Color-Red and T.delete[File]
		eventually T.restore[File]
	}
	eventually always no reactions
} for exactly 1 File, exactly 3 Color, 10 Action, 10 Reaction expect 1


// Reactions

/*
reaction empty_clear
when
	T.empty[]
where
	f in T.trashed
then
	L.clear[f]
*/

sig Empty_Clear extends Reaction { file : File }
fact {
	all x,y : Empty_Clear | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some d : Empty_Clear & reactions_to_add | d.file = f) iff (T.empty[] and f in T.trashed)
		(some d : Empty_Clear & reactions_to_remove | d.file = f) iff L.clear[f]
	}
}	

/*
reaction delete_affix
when
	T.delete[f]
then
	L.affix[f,Red]
*/

sig Delete_Affix extends Reaction { file : File }
fact {
	all x,y : Delete_Affix | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some d : Delete_Affix & reactions_to_add | d.file = f) iff T.delete[f]
		(some d : Delete_Affix & reactions_to_remove | d.file = f) iff L.affix[f,Red]
	}
}

/*
reaction restore_detach
when
	T.restore[f]
then
	L.detach[f,Red]
*/

sig Restore_Detach extends Reaction { file : File }
fact {
	all x,y : Restore_Detach | x.file = y.file implies x = y
}
fact {
	all f : File | always {
		(some d : Restore_Detach & reactions_to_add | d.file = f) iff T.restore[f]
		(some d : Restore_Detach & reactions_to_remove | d.file = f) iff L.detach[f,Red]
	}
}	

/*
reaction affix_error
when
	L.affix[f,c]
where
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

/*
reaction affix_red_error
when
	L.affix[f,Red]
where
	f in T.accessible
then
	error
*/

sig Affix_Red_Error extends Reaction { }
fact {
	all x,y : Affix_Red_Error | x = y
}
fact {
	always {
		(some Affix_Red_Error & reactions_to_add) iff (some f : File | L.affix[f,Red] and f in T.accessible)
		(some Affix_Red_Error & reactions_to_remove) iff error
	}
}

/*
reaction detach_red_error
when
	L.detach[f,Red]
where
	f in T.trashed
then
	error
*/

sig Detach_Red_Error extends Reaction { }
fact {
	all x,y : Detach_Red_Error | x = y
}
fact {
	always {
		(some Detach_Red_Error & reactions_to_add) iff (some f : File | L.detach[f,Red] and f in T.trashed)
		(some Detach_Red_Error & reactions_to_remove) iff error
	}
}

/*
reaction clear_red_error
when
	L.clear[f]
where
	f in T.trashed and Red in f.colors
then
	error
*/

sig Clear_Red_Error extends Reaction { }
fact {
	all x,y : Clear_Red_Error | x = y
}
fact {
	always {
		(some Clear_Red_Error & reactions_to_add) iff (some f : File | L.clear[f] and f in T.trashed and Red in f.colors)
		(some Clear_Red_Error & reactions_to_remove) iff error
	}
}
