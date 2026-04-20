module NoSecretsInTrash2
open Action
open Reaction

// App configuration

// User concepts
open Trash[File]

one sig T extends Trash {}

// Items are files and some of them are secrets
sig File {}
sig Secret extends File {}

// Projections of the state of the concepts to simplify the specification and visualization

fun accessible : set File { T.accessible }
fun trashed : set File { T.trashed }

// The app invariant

// Secret files cannot be in the trash
// Accessible files were created or restored by a normal user
// Trashed non-secret files were deleted by a normal user
check Invariant {
	always {
		no reactions iff {
			no Secret & trashed
			accessible = { f : File | before (not T.delete[f] since (T.create[f] or (T.restore[f] and no Secret & trashed))) }
		} 
	}
} for 2 but 10 Action, 10 Reaction expect 0

// Scenarios

// Without concurrent requests we cannot have more than one secret
// file in the trash, so the following scenario is impossible
run Scenario1 {
	Secret = File
	eventually Secret in trashed
	eventually always no reactions		
} for exactly 3 File, 10 Action, 10 Reaction expect 0

// At some point a secret file is deleted when some non secret fine is in the trash
// Then a reaction will first restore the non secret files, empty the trash, and finally delete again the restored files
run Scenario2 {
	one Secret
	eventually (File - Secret in trashed and T.delete[Secret])
	eventually always no reactions		
} for exactly 3 File, 9 Action, 5 Reaction, 13 steps expect 1

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

sig Delete_Empty extends Reaction {}
fact {
	all x,y : Delete_Empty | x = y
	eventually { some f : File | T.delete[f] and f in Secret } implies some Delete_Empty
}

fun delete_empty_add : set Reaction { { d : Delete_Empty | some f : File | T.delete[f] and f in Secret } }
fun delete_empty_remove : set Reaction { { d : Delete_Empty | T.empty[] } }

/*
reaction delete_restore
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.restore[g]
*/

sig Delete_Restore extends Reaction { g : File }
fact {
	all x,y : Delete_Restore | x.g = y.g implies x = y
	all x : File | eventually { some f : File | T.delete[f] and f in Secret and x in trashed - Secret } implies some d : Delete_Restore | d.g = x
}
fun delete_restore_add : set Reaction { { d : Delete_Restore | some f : File | T.delete[f] and f in Secret and d.g in trashed - Secret } }
fun delete_restore_remove : set Reaction { { d : Delete_Restore | T.restore[d.g] } }

/*
reaction delete_delete
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.delete[g]
*/

sig Delete_Delete extends Reaction { g : File }
fact {
	all x,y : Delete_Delete | x.g = y.g implies x = y
	all x : File | eventually { some f : File | T.delete[f] and f in Secret and x in trashed - Secret } implies some d : Delete_Delete | d.g = x
}
fun delete_delete_add : set Reaction { { d : Delete_Delete | some f : File | T.delete[f] and f in Secret and d.g in trashed - Secret } }
fun delete_delete_remove : set Reaction { { d : Delete_Delete | T.delete[d.g] } }

// Reaction semantics

fun reactions_to_add : set Reaction { delete_empty_add + delete_restore_add + delete_delete_add }
fun reactions_to_remove : set Reaction { delete_empty_remove + delete_restore_remove + delete_delete_remove }

fact {
	no reactions
	always {
		// Priority to reactions
		some reactions implies some reactions & reactions_to_remove
		reactions' = (reactions - reactions_to_remove) + reactions_to_add
	}
}

// Preventions

/*
when
	T.empty[]
require
	no trashed - Secret
*/

fact {
	always {
		T.empty[] implies no trashed - Secret
	}
}
