module Apps/FileSystem1

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

sig File {}
sig Color {}

// The app invariant

// Only accessible files can have colors
check Invariant {
	always {
		not syncing iff labels.Color in accessible
	}
} for 2 but 7 Action

// Scenarios

// One file will all possible colors is deleted and not restored
// Syncronization will clear all colors
run Scenario {
	eventually (some f : File | f.labels = Color and delete[f] and always not restore[f])
	eventually always not syncing
} for 1 File, exactly 3 Color, 7 Action expect 1

// When is the app syncing
pred syncing {
	sync_delete	
}

// For visualization only
one sig Syncing {}
fun syncing : Syncing { { s : Syncing | syncing } } 

// Syncronization rules

/*
when
	affix[f,c]
require
	f in accessible
*/

fact {
	all f : File, c : Color | always {
		affix[f,c] implies f in accessible
	}
}

/*
when
	delete[f]
where
	some f.labels
then
	clear[f] or restore[f]
*/

pred sync_delete {
	some f : File | before ((not clear[f] and not restore[f]) since (delete[f] and some f.labels))
}

/*
when
	detach[f,l]
require
	f in acessible
*/

fact {
	all f : File, c : Color | always {
		detach[f,c] implies f in accessible
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
