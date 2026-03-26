module Apps/FileSystem3
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

// Single user with a single trash and labels

one sig U extends User {}
one sig T extends Trash {}
one sig L extends Label {}

// Types

sig File {}
sig Color {}
one sig Red extends Color {}

// App specific relations

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }
fun colors : File -> set Color { L.labels }

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
	eventually (File.colors = Color-Red and T.delete[User,File])
	eventually (no Reaction and File in trashed and T.empty[User])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 3 Reaction expect 1

// One file will all possible colors is deleted and later restored
// Reactions will affix the red color to the trashed file and then remove the red color
run Scenario2 {
	eventually (File.colors = Color-Red and T.delete[User,File])
	eventually (no Reaction and T.restore[User,File])
	eventually always no Reaction
} for exactly 1 File, exactly 3 Color, 7 Action, 3 Reaction expect 1


// Reactions

/*
when
	T.empty[User]
where
	f in trashed and some f.colors
then
	L.clear[User,f]
*/

var lone sig EmptyClear extends Reaction { }

fact {
	always {
		some EmptyClear iff {
			some f : File | before {
				not L.clear[User,f] since (T.empty[User] and f in trashed and some f.colors)
			}
		}
	}
}

/*
when
	T.delete[User,f]
where
	Red not in f.colors
then
	L.affix[User,f,Red] or T.empty[User] or T.restore[User,f]
*/

var lone sig DeleteAffixOrEmptyOrRestore extends Reaction { }

fact {
	always {
		some DeleteAffixOrEmptyOrRestore iff {
			some f : File | before {
				not (L.affix[User,f,Red] or T.empty[User] or T.restore[User,f]) since (T.delete[User,f] and Red not in f.colors)
			}
		}
	}
}

/*
when
	T.restore[User,f]
where
	Red in f.colors
then
	L.detach[User,f,Red] or T.delete[User,f] or L.clear[User,f]
*/

var lone sig RestoreDetachOrDeleteOrClear extends Reaction { }

fact {
	always {
		some RestoreDetachOrDeleteOrClear iff {
			some f : File | before {
				not (L.detach[User,f,Red] or T.delete[User,f] or L.clear[User,f]) since (T.restore[User,f] and Red in f.colors)
			}
		}
	}
}

// Preventions

/*
when
	L.affix[User,f,c]
require
	f in accessible+trashed
*/

fact {
	all f : File, c : Color | always {
		L.affix[User,f,c] implies f in accessible+trashed
	}
}

/*
when
	L.affix[User,f,Red]
require
	f not in accessible
*/

fact {
	all f : File | always {
		L.affix[User,f,Red] implies f not in accessible
	}
}


/*
when
	L.detach[User,f,c]
require
	f in accessible+trashed
*/

fact {
	all f : File, c : Color | always {
		L.detach[User,f,c] implies f in accessible+trashed
	}
}

/*
when
	L.detach[User,f,Red]
require
	f not in trashed
*/

fact {
	all f : File | always {
		L.detach[User,f,Red] implies f not in trashed
	}
}

/*
when
	L.clear[User,f]
require
	f not in trashed or Red not in f.colors
*/

fact {
	all f : File | always {
		L.clear[User,f] implies (f not in trashed or Red not in f.colors)
	}
}

/*
when
	T.create[User,f]
require
	no f.colors
*/

fact {
	all f : File | always {
		T.create[User,f] implies no f.colors
	}
}
