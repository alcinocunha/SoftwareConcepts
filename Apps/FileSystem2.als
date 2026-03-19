module Apps/FileSystem2

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

sig File {}
sig Color {}

// The app invariant

// Colors can be assigned to both accessible and trashed files
check Invariant {
	always {
		not syncing iff labels.Color in accessible+trashed
	}
} for 2 but 7 Action

// Scenarios

// One file will all possible colors is deleted and the trash is emptied
// Syncronization will clear all colors
run Scenario {
	eventually (some f : File | f.labels = Color and empty and always not restore[f])
	eventually always not syncing
} for 1 File, exactly 3 Color, 7 Action expect 1

// When is the app syncing
pred syncing {
	sync_empty	
}

// For visualization only
one sig Syncing {}
fun syncing : Syncing { { s : Syncing | syncing } } 

// Synchronization rules

/*
when
	affix[f,c]
require
	f in accessible+trashed
*/

fact {
	all f : File, c : Color | always {
		affix[f,c] implies f in accessible+trashed
	}
}

/*
when
	detach[f,c]
require
	f in accessible+trashed
*/

fact {
	all f : File, c : Color | always {
		detach[f,c] implies f in accessible+trashed
	}
}

/*
when
	empty
where
	f in trashed
	some f.labels
then
	clear[f]
*/

pred sync_empty {
	some f : File | before {
		not clear[f] since (empty and f in trashed and some f.labels)
	}
}


/*
when
	create[f]
require
	no f.labels
*/

fact {
	all f : File | always {
		create[f] implies no f.labels
	}
}

