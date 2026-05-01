module Apps/WPR/FileSystem
open Action
open Reaction

// App configuration

// Composed concepts

open Concepts/Trash[Object]
open Concepts/Owning[Dir,Other]

one sig O extends Owning {}
one sig Root extends Trash {}
sig Other extends Trash {}

// Types

abstract sig Object {}
sig File, Dir extends Object {}

// Projections

fun content : Dir -> Other { O.owns }

// This app assumes reactions have priority over requests

fact {
	PriorityToReactions
}

// The design goal

// Only accessible files can have colors
check Design {
	always {
		no reactions iff {
            // The non root trashes have objects if they are owned by some directory
			all t : Other | some t.(accessible+trashed) implies some content.t
            // A directory owns a trash iff it is in some trash
            all d : Dir | some d.content iff some (accessible+trashed).d
            // A directory can only be in one trash and can only contain one trash
            all d : Dir | lone (accessible+trashed).d and lone d.content
            // No cycles
            all d : Dir | d not in d.^(content.(accessible+trashed))
		}
	}
} for 1 File, 2 Dir, 2 Other, 10 Action, 10 Reaction expect 0

// Reactions

/*
reaction create_dir
when 
    t.create(d)
where
    d in Dir
then
    some t : Other | O.acquire(d,t)
*/

sig create_dir extends Reaction { dir : Object }
fact {
	all x,y : create_dir | x.dir = y.dir implies x = y
}
fact {
	all d : Object | always {
		(some r : create_dir & reactions_to_add | r.dir = d) iff (some t : Trash | t.create[d] and d in Dir)
        (some r : create_dir & reactions_to_remove | r.dir = d) iff (some t : Other | O.acquire[d,t])
	}
}

/*
reaction empty_dir
when
    t.empty()
where
    d in t.trashed and x in d.content
then
    O.release(d,x)
*/

sig empty_dir extends Reaction { dir : Dir, trash : Trash }
fact {
    all x,y : empty_dir | x.dir = y.dir and x.trash = y.trash implies x = y
}
fact {
    all d : Dir, x : Trash | always {
        (some r : empty_dir & reactions_to_add | r.dir = d) iff (some t : Trash | t.empty[] and d in t.trashed and x in d.content)
        (some r : empty_dir & reactions_to_remove | r.dir = d) iff (O.release[d,x])
    }
}

/*
reaction release_trash_delete_objects
when
    O.release(d,t)
where
    o in t.accessible
then
    t.delete(o)
*/

sig release_trash_delete_objects extends Reaction { trash : Trash, object : Object }
fact {
    all x,y : release_trash_delete_objects | x.trash = y.trash and x.object = y.object implies x = y
}
fact {
    all t : Trash, o : Object | always {
        (some r : release_trash_delete_objects & reactions_to_add | r.trash = t and r.object = o) iff (some d : Dir | O.release[d,t] and o in t.accessible)
        (some r : release_trash_delete_objects & reactions_to_remove | r.trash = t and r.object = o) iff (t.delete[o])
    }
}

/*
reaction release_trash_empty
when
    O.release(d,t)
where
    no t.accessible and some t.trashed
then
    t.empty()
*/

sig release_trash_empty extends Reaction { trash : Trash }
fact {
    all x,y : release_trash_empty | x.trash = y.trash implies x = y
}
fact {
    all t : Trash | always {
        (some r : release_trash_empty & reactions_to_add | r.trash = t) iff (some d : Dir | O.release[d,t] and no t.accessible and some t.trashed)
        (some r : release_trash_empty & reactions_to_remove | r.trash = t) iff (t.empty[])
    }
}

/*
reaction delete_last_empty
when
    t.delete(o)
where
    t not in Root and no content.t and t.accessible in o
then
    t.empty()
*/

sig delete_last_empty extends Reaction { trash : Trash }
fact {
    all x,y : delete_last_empty | x.trash = y.trash implies x = y
}
fact {
    all t : Trash | always {
        (some r : delete_last_empty & reactions_to_add | r.trash = t) iff (some o : Object | t.delete[o] and t not in Root and no content.t and t.accessible in o)
        (some r : delete_last_empty & reactions_to_remove | r.trash = t) iff (t.empty[])
    }
}

/*
reaction acquire_error
when
    O.acquire(o,t)
where
    o in File or no (accessible+trashed).o or some o.content or some t.(accessible+trashed)
then
    error
*/

sig acquire_error extends Reaction {}
fact {
    all x,y : acquire_error | x = y
}
fact {
    always {
        (some acquire_error & reactions_to_add) iff (some o : Object, t : Trash | O.acquire[o,t] and (o in File or no (accessible+trashed).o or some o.content or some t.(accessible+trashed)))
        (some acquire_error & reactions_to_remove) iff error
    }
}

/*
reaction create_error
when
    t.create(o)
where
    t not in Root and no content.t
then
    error
*/

sig create_error extends Reaction {}
fact {
    all x,y : create_error | x = y
}
fact {
    always {
        (some create_error & reactions_to_add) iff (some t : Trash, o : Object | t.create[o] and t not in Root and no content.t)
        (some create_error & reactions_to_remove) iff error
    }
}

/*
reaction release_error
when
    O.release(d,t)
where
    some (accessible+trashed).d
then
    error
*/

sig release_error extends Reaction {}
fact {
    all x,y : release_error | x = y
}
fact {
    always {
        (some release_error & reactions_to_add) iff (some d : Dir, t : Trash | O.release[d,t] and some (accessible+trashed).d)
        (some release_error & reactions_to_remove) iff error
    }
}
