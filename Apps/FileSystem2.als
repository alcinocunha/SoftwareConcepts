module Apps/FileSystem2

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

sig File {}
sig Color {}

// The app invariant

check Invariant {
	always {
		not syncing iff labels.Color in accessible+trashed
	}
} for 2 but 7 Action

// Scenarios

run Scenario {
	eventually (File in trashed and File.labels = Color and File = labels.Color and empty and after eventually not syncing)
} for exactly 2 File, exactly 2 Color, 7 Action expect 1

run AlwaysSyncing {
	eventually (always (syncing and some Action))
} for 2 but 7 Action

check Clear {
	always {
		all f : File | clear[f] and f not in accessible+trashed implies syncing 
	}
} for 2 but 7 Action

// Synchronization rules


/*
when
	Label.affix(f,c)
where
	in Trash: f not in accessible+trashed
then
	error
*/

fact {
	all f : File, c : Color | always {
		affix[f,c] and f not in accessible+trashed implies error
	}
}

/*
when
	Label.detach(f,c)
where
	in Trash: f not in accessible+trashed
then
	error
*/

fact {
	all f : File, c : Color | always {
		detach[f,c] and f not in accessible+trashed implies error
	}
}

/*
when
	Trash.empty
where
	in Trash: f in trashed
	in Label: some f.labels
then
	Label.clear(f)
*/

pred sync_empty {
	some f : File | before (not clear[f] since (empty and f in trashed and some f.labels))
}


/*
when
	Trash.create(f)
when
	in Labels: some f.labels
then
	error
*/

fact {
	all f : File | always {
		create[f] and some f.labels implies error
	}
}

// When is the app syncing

pred syncing {
	sync_empty	
}

// For visualization only
one sig Syncing {}
fun syncing : Syncing { { s : Syncing | syncing } } 
