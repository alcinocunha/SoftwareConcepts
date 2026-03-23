module Apps/FileSystem2
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

// Colors can be assigned to both accessible and trashed files
check Invariant {
	always {
		no Reaction iff labels.Color in accessible+trashed
	}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// Two files with colors are deleted and the trash is emptied
// Then a reaction will clear all colors of all files
run Scenario {
	eventually (File in User.trashed and User.labels.Color = File and empty[User])
	eventually always no Reaction
} for exactly 2 File, exactly 3 Color, 7 Action, 1 Reaction expect 1

// Reactions

/*
when
	empty[User]
where
	f in User.trashed and some User.labels[f]
then
	clear[User,f]
*/

var lone sig EmptyClear extends Reaction { }

fact {
	always {
		some EmptyClear iff {
			some f : File | before {
				not clear[User,f] since (empty[User] and f in User.trashed and some User.labels[f])
			}
		}
	}
}

// Preventions

/*
when
	affix[User,f,c]
require
	f in User.(accessible+trashed)
*/

fact {
	all f : File, c : Color | always {
		affix[User,f,c] implies f in User.(accessible+trashed)
	}
}

/*
when
	detach[User,f,c]
require
	f in User.(accessible+trashed)
*/

fact {
	all f : File, c : Color | always {
		detach[User,f,c] implies f in User.(accessible+trashed)
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

