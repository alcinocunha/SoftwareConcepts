module Apps/FileSystem3

// Composed concepts

open Concepts/Trash[File]
open Concepts/Label[File,Color]

sig File {}
sig Color {}

one sig Red extends Color {}

// The app invariant

check Invariant {
	always {
		not syncing iff {
			labels.Color in accessible+trashed
			labels.Red = trashed
		}
	}
} for 2 but 7 Action

// Scenarios

run Scenario {
	eventually (File in trashed and File.labels = Color and File = labels.Color and empty and after eventually not syncing)
} for exactly 2 File, exactly 2 Color, 7 Action expect 1

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
	Label.affix(f,Red)
where
	in Trash: f in accessible
then
	error
*/

fact {
	all f : File | always {
		affix[f,Red] and f in accessible implies error
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
	Label.detach(f,Red)
where
	in Trash: f in rashed
then
	error
*/

fact {
	all f : File | always {
		detach[f,Red] and f in trashed implies error
	}
}

/*
when
	Label.clear(f)
where
	in Trash: f in rashed
	in Label: Red in f.labels
then
	error
*/

fact {
	all f : File | always {
		clear[f] and f in trashed and Red in f.labels implies error
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

/*
when
	Trash.delete(f)
where
	in Label: Red not in f.labels
then
	Label.affix(f,Red) or Trash.empty or Trash.restore(f)
*/

pred sync_delete {
	some f : File | before ((not affix[f,Red] and not empty and not restore[f]) since (delete[f] and Red not in f.labels))
}

/*
when
	Trash.restore(f)
where
	in Label: Red in f.labels
then
	Label.detach(f,Red) or Trash.delete(f) or Label.clear(f)
*/

pred sync_restore {
	some f : File | before ((not detach[f,Red] and not delete[f] and not clear[f]) since (restore[f] and Red in f.labels))
}
