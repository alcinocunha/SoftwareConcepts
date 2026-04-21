module Apps/WPR/NoSecretsInTrash2
open Action
open Reaction

// App configuration

// User concepts

open Concepts/Trash[File]

one sig T extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// Projections of the state of the concepts to simplify the specification and visualization

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }

// This app assumes reactions have priority over requests

fact {
	PriorityToReactions
}

// The app invariant

// Secret files cannot be in the trash
// Accessible files were created or restored by a normal user
// Trashed non-secret files were deleted by a normal user
check Invariant {
	always {
		no reactions iff {
			trashed = { f : File - Secret | before (not ((T.empty[] or T.restore[f]) and no Secret & trashed) since T.delete[f]) }
			accessible = { f : File | before (not T.delete[f] since (T.create[f] or (T.restore[f] and no Secret & trashed))) }
		} 
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Additional properties

check Invariant {
	no reactions implies {
		no Secret & trashed
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// At some point a secret file is deleted when some non secret fine is in the trash
// Then a reaction will first restore the non secret files, empty the trash, and finally delete again the restored files
run Scenario1 {
	one Secret
	eventually (File - Secret in trashed and T.delete[Secret])
	eventually always no reactions		
} for exactly 3 File, 10 Action, 10 Reaction, 13 steps expect 1

// Without concurrent requests we cannot have more than one secret
// file in the trash, so the following scenario is impossible
run Scenario2 {
	Secret = File
	eventually Secret in trashed
	eventually always no reactions		
} for exactly 3 File, 10 Action, 10 Reaction expect 0

// Reactions

/*
reaction delete_empty
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]
*/

lone sig Delete_Empty extends Reaction {}
fact {
	always {
		some Delete_Empty & reactions_to_add iff some f : File | T.delete[f] and f in Secret
		some Delete_Empty & reactions_to_remove iff T.empty[]
	}
}

/*
reaction delete_restore
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.restore[g]
*/

sig Delete_Restore extends Reaction { file : File }
fact {
	all x,y : Delete_Restore | x.file = y.file implies x = y
}
fact {
	all g : File | always {
		(some d : Delete_Restore & reactions_to_add | d.file = g) iff (some f : File | T.delete[f] and f in Secret and g in trashed - Secret)
		(some d : Delete_Restore & reactions_to_remove | d.file = g) iff T.restore[g]
	}
}

/*
reaction delete_delete
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.delete[g]
*/

sig Delete_Delete extends Reaction { file : File }
fact {
	all x,y : Delete_Delete | x.file = y.file implies x = y
}
fact {
	all g : File | always {
		(some d : Delete_Delete & reactions_to_add | d.file = g) iff (some f : File | T.delete[f] and f in Secret and g in trashed - Secret)
		(some d : Delete_Delete & reactions_to_remove | d.file = g) iff T.delete[g]
	}
}

/*
reaction empty_error
when
	T.empty[]
where
	some Secret & trashed and some trashed - Secret
then
	error
*/

lone sig Empty_Error extends Reaction {}
fact {
	always {
		some Empty_Error & reactions_to_add iff (T.empty[] and some Secret & trashed and some trashed - Secret)
		some Empty_Error & reactions_to_remove iff error
	}
}


