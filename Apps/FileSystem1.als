module Apps/FileSystem1
open Action[User]
open Reaction

// Composed concepts

open Concepts/Trash[User,File]
open Concepts/Label[User,File,Color]

// Single user app

one sig User {}

// Types

sig File {}
sig Color {}

// The app invariant

// Only accessible files can have colors
check Invariant {
	always {
		no Reaction iff labels.Color in accessible
	}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// One files with all colors is deleted
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (User.labels[File] = Color and delete[User,File])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 1 Reaction expect 1

// Reactions

/*
when
	delete[User,f]
where
	some User.labels[f]
then
	clear[User,f] or restore[User,f]
*/

var lone sig DeleteClearOrRestore extends Reaction { }

fact {
	always {
		some DeleteClearOrRestore iff {
			some f : File | before (not (clear[User,f] or restore[User,f]) since (delete[User,f] and some User.labels[f]))
		}
	}
}

// Preventions

/*
when
	affix[User,f,c]
require
	f in User.accessible
*/

fact {
	all f : File, c : Color | always {
		affix[User,f,c] implies f in User.accessible
	}
}

/*
when
	detach[User,f,c]
require
	f in User.accessible
*/

fact {
	all f : File, c : Color | always {
		detach[User,f,c] implies f in User.accessible
	}
}

/*
when
	create[User,f]
require
	no User.labels[f]
*/

fact {
	all f : File | always {
		create[User,f] implies no User.labels[f]
	}
}
