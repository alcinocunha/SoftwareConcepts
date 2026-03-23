module Apps/FileSystem3
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
one sig Red extends Color {}

// The app invariant

// Colors can be assigned to both accessible and trashed files
// and trashed files have the red color
check Invariant {
	always {
		no Reaction iff {
			labels.Color in accessible+trashed
			labels.Red = trashed
		}
	}
} for 2 but 7 Action, 3 Reaction expect 0

// Scenarios

// One file will all possible colors is deleted and later the trash is emptied
// Reactions will affix the red color to the trashed file and then clear all its colors
run Scenario1 {
	eventually (User.labels[File] = Color-Red and delete[User,File])
	eventually (no Reaction and File in User.trashed and empty[User])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 3 Reaction expect 1

// One file will all possible colors is deleted and later restored
// Reactions will affix the red color to the trashed file and then remove the red color
run Scenario2 {
	eventually (User.labels[File] = Color-Red and delete[User,File])
	eventually (no Reaction and restore[User,File])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 3 Reaction expect 1


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

/*
when
	delete[User,f]
where
	Red not in User.labels[f]
then
	affix[User,f,Red] or empty[User] or restore[User,f]
*/

var lone sig DeleteAffixOrEmptyOrRestore extends Reaction { }

fact {
	always {
		some DeleteAffixOrEmptyOrRestore iff {
			some f : File | before {
				not (affix[User,f,Red] or empty[User] or restore[User,f]) since (delete[User,f] and Red not in User.labels[f])
			}
		}
	}
}

/*
when
	restore[User,f]
where
	Red in User.labels[f]
then
	detach[User,f,Red] or delete[User,f] or clear[User,f]
*/

var lone sig RestoreDetachOrDeleteOrClear extends Reaction { }

fact {
	always {
		some RestoreDetachOrDeleteOrClear iff {
			some f : File | before {
				not (detach[User,f,Red] or delete[User,f] or clear[User,f]) since (restore[User,f] and Red in User.labels[f])
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
	affix[User,f,Red]
require
	f not in User.accessible
*/

fact {
	all f : File | always {
		affix[User,f,Red] implies f not in User.accessible
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
	detach[User,f,Red]
require
	f not in User.trashed
*/

fact {
	all f : File | always {
		detach[User,f,Red] implies f not in User.trashed
	}
}

/*
when
	clear[User,f]
require
	f not in User.trashed or Red not in User.labels[f]
*/

fact {
	all f : File | always {
		clear[User,f] implies (f not in User.trashed or Red not in User.labels[f])
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
