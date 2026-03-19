module Apps/FileSystem3

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

sig File {}
sig Color {}
one sig Red extends Color {}

// The app invariant

// Colors can be assigned to both accessible and trashed files
// and trashed files have the red color
check Invariant {
	always {
		not syncing iff {
			labels.Color in accessible+trashed
			labels.Red = trashed
		}
	}
} for 2 but 7 Action

// Scenarios

// One file will all possible colors is deleted and the trash is emptied
// Syncronization will clear all colors
run Scenario {
	eventually (some f : File | f.labels = Color and empty)
	eventually always not syncing
} for 1 File, exactly 3 Color, 7 Action expect 1

// When is the app syncing

pred syncing {
	sync_empty or sync_delete or sync_restore
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
	affix[f,Red]
require
	f not in accessible
*/

fact {
	all f : File | always {
		affix[f,Red] implies f not in accessible
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
	detach[f,Red]
require
	f not in trashed
*/

fact {
	all f : File | always {
		detach[f,Red] implies f not in trashed
	}
}

/*
when
	clear[f]
require
	f not in trashed or Red not in f.labels
*/

fact {
	all f : File | always {
		clear[f] implies (f not in trashed or Red not in f.labels)
	}
}

/*
when
	empty
where
	f in trashed and some f.labels
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

/*
when
	delete[f]
where
	Red not in f.labels
then
	affix[f,Red] or empty or restore[f]
*/

pred sync_delete {
	some f : File | before {
		not (affix[f,Red] or empty or restore[f]) since (delete[f] and Red not in f.labels)
	}
}

/*
when
	restore[f]
where
	Red in f.labels
then
	detach[f,Red] or delete[f] or clear[f]
*/

pred sync_restore {
	some f : File | before {
		not (detach[f,Red] or delete[f] or clear[f]) since (restore[f] and Red in f.labels)
	}
}
