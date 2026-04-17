module Apps/WPR/FileSystem3
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

// Priority of reactions over requests

fact {
	PriorityToReactions
}

// The app invariant

// Colors can be assigned to both accessible and trashed files
// and trashed files have the red color
check Invariant {
	always {
		no Reaction iff {
			colors.Color in accessible+trashed
			colors.Red = trashed
		}
	}
} for 2 but 7 Action, 3 Reaction expect 0

// Scenarios

// One file will all possible colors is deleted and later the trash is emptied
// Reactions will affix the red color to the trashed file and then clear all its colors
run Scenario1 {
	eventually (File.colors = Color-Red and T.delete[File])
	eventually (no Reaction and File in trashed and T.empty[])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 3 Reaction expect 1

// One file will all possible colors is deleted and later restored
// Reactions will affix the red color to the trashed file and then remove the red color
run Scenario2 {
	eventually (File.colors = Color-Red and T.delete[File])
	eventually (no Reaction and T.restore[File])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 3 Reaction expect 1


// Reactions

/*
reaction EmptyClear[f : File]
when
	T.empty[]
where
	f in trashed
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
				not L.clear[f] since (T.empty[] and f in trashed)
			}
		}
	}
}

/*
reaction DeleteAffix[f : File]
when
	T.delete[f]
then
	L.affix[f,Red]
*/

var sig DeleteAffix extends Reaction { var f : File }

fact {
	always all r : DeleteAffix {
		all d : DeleteAffix' | d.f' = r.f implies d = r
	}
}
pred DeleteAffix [x : File] { some d : DeleteAffix | d.f = x }

fact {
	all f : File | always {
		DeleteAffix[f] iff {
			before {
				not L.affix[f,Red] since (T.delete[f] and Red not in f.colors)
			}
		}
	}
}

/*
reaction RestoreDetach[f : File]
when
	T.restore[f]
then
	L.detach[f,Red]
*/

var sig RestoreDetach extends Reaction { var f : File }

fact {
	always all r : RestoreDetach {
		all d : RestoreDetach' | d.f' = r.f implies d = r
	}
}
pred RestoreDetach [x : File] { some d : RestoreDetach | d.f = x }

fact {
	all f : File | always {
		RestoreDetach[f] iff {
			before {
				not L.detach[f,Red] since T.restore[f]
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
	L.affix[f,Red]
require
	f not in accessible
*/

fact {
	all f : File | always {
		L.affix[f,Red] implies f not in accessible
	}
}

/*
when
	L.detach[f,Red]
require
	f not in trashed
*/

fact {
	all f : File | always {
		L.detach[f,Red] implies f not in trashed
	}
}

/*
when
	L.clear[f]
require
	f not in trashed or Red not in f.colors
*/

fact {
	all f : File | always {
		L.clear[f] implies f not in trashed or Red not in f.colors
	}
}
