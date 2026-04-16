module Apps/WPR/Zoomy

open Action
open Reaction

// App configuration

open Concepts/Meeting[User]
open Concepts/Chat[User,Content]
open Concepts/Owning[User,Meeting] as OM
open Concepts/Owning[Meeting,Chat] as OC

one sig OM extends OM/Owning {}
one sig OC extends OC/Owning {}

// Types

sig User {}
sig Content {}

// Projections of the state of the concepts to simplify the specification and visualization

fun scheduled : User -> Meeting { OM.owns }
fun chat : Meeting -> Chat { OC.owns }

// Priority of reactions over requests

fact {
    PriorityToReactions
}

// The app invariant

check Invariant {
    always {
        no Reaction iff {
            host in ~scheduled
            chat in host.User -> one Chat
			joined.Time = ~chat.participants
        }
    }
} for 2 but 13 Action, 5 Reaction, 1 Meeting, 1 Chat, 14 steps expect 0

// The following does not hold but there is no problem because one can only read messages sent after joining
check AcquireNoMessage {
    always {
        all m : Meeting, c : Chat | OC.acquire[m,c] implies no c.messages
    }
} for 1 but 13 Action, 5 Reaction, 1 Meeting, 1 Chat, 12 steps expect 1

check AcquireNoJoined {
    always {
        all m : Meeting, c : Chat | OC.acquire[m,c] implies no c.joined
    }
} for 1 but 13 Action, 5 Reaction, 1 Meeting, 1 Chat, 12 steps expect 0

check SendSafe {
    always {
        all c : Chat, u : User, m : Message | c.send[u,m] implies u in (chat.c).participants
    }
} for 1 but 13 Action, 5 Reaction, 1 Meeting, 1 Chat, 12 steps expect 0

// Scenarios

run Scenario {
    // Eventually an user sends a message and later the respective meeting ends
    some c : Chat, u : User, m : Message | eventually {
        c.send[u,m]
        eventually (chat.c).end[u]
    }
    eventually always no Reaction
} for 2 but 11 Action, 5 Reaction, 1 Meeting, 1 Chat, 11 steps expect 1

// Reactions

/*
reaction StartMeeting[m]
when
    m.start[u]
then
    some c : Chat | OC.acquire[m,c]
*/

var sig StartMeeting extends Reaction { var m : Meeting }
fact {
	always all r : StartMeeting {
		all d : StartMeeting' | d.m' = r.m implies d = r
	}    
}
pred StartMeeting [x : Meeting] { some r : StartMeeting | r.m = x }

fact {
    all m : Meeting | always {
        StartMeeting[m] iff some u : User | before {
            not (some c : Chat | OC.acquire[m,c]) since m.start[u]
        }
    }
}

/*
reaction EndMeeting[m]
when
    m.end[u]
then
    OC.release[m,c]
*/

var sig EndMeeting extends Reaction { var m : Meeting }
fact {
    always all r : EndMeeting {
        all d : EndMeeting' | d.m' = r.m implies d = r
    }    
}
pred EndMeeting [x : Meeting] { some r : EndMeeting | r.m = x }

fact {
    all m : Meeting | always {
        EndMeeting[m] iff some u : User, c : Chat | before {
            not OC.release[m,c] since m.end[u]
        }
    }
}

/*
reaction EndMeetingForceLeaving[m,u]
when
    m.end[h]
where
    c in m.chat and u in c.joined.Time
then
    c.leave[u]
*/

var sig EndMeetingForceLeaving extends Reaction { var m : Meeting, var u : User }
fact {
    always all r : EndMeetingForceLeaving {
        all d : EndMeetingForceLeaving' | d.m' = r.m and d.u' = r.u implies d = r
    }    
}
pred EndMeetingForceLeaving [x : Meeting, y : User] { some r : EndMeetingForceLeaving | r.m = x and r.u = y }

fact {
    all m : Meeting, u : User | always {
        EndMeetingForceLeaving[m,u] iff some h : User, c : Chat | before {
            not c.leave[u] since (m.end[h] and c in m.chat and u in c.joined.Time)
        }
    }
}

/*
reaction JoinMeeting[m,u]
when
    m.join[u]
where
    c in m.chat
then
    c.join[u]
*/

var sig JoinMeeting extends Reaction { var m : Meeting, var u : User }
fact {
    always all r : JoinMeeting {
        all d : JoinMeeting' | d.m' = r.m and d.u' = r.u implies d = r
    }
}
pred JoinMeeting [x : Meeting, y : User] { some r : JoinMeeting | r.m = x and r.u = y }

fact {
    all m : Meeting, u : User | always {
        JoinMeeting[m,u] iff some c : Chat | before {
            not c.join[u] since (m.join[u] and c in m.chat)
        }
    }
}

/*
reaction LeaveMeeting[m,u]
when
    m.leave[u]
where
    c in m.chat
then
    c.leave[u]
*/

var sig LeaveMeeting extends Reaction { var m : Meeting, var u : User }
fact {
    always all r : LeaveMeeting {
        all d : LeaveMeeting' | d.m' = r.m and d.u' = r.u implies d = r
    }
}
pred LeaveMeeting [x : Meeting, y : User] { some r : LeaveMeeting | r.m = x and r.u = y }

fact {
    all m : Meeting, u : User | always {
        LeaveMeeting[m,u] iff some c : Chat | before {
            not c.leave[u] since (m.leave[u] and c in m.chat)
        }
    }
}


// Preventions

/*
when
    m.start[u]
require
    m in u.scheduled
*/

fact {
    all m : Meeting, u : User | always {
        m.start[u] implies m in u.scheduled
    }
}

/*
when
    OM.release[u,m]
require
    no m.host
*/

fact {
    all m : Meeting, u : User | always {
        OM.release[u,m] implies no m.host
    }
}

/*
when
    c.join[u]
require
    some (chat.c).host and u in (chat.c).participants
*/

fact {
    all c : Chat, u : User | always {
        c.join[u] implies some (chat.c).host and u in (chat.c).participants
    }
}

/*
when
    c.leave[u]
require
    u not in (chat.c).participants
*/

fact {
    all c : Chat, u : User | always {
        c.leave[u] implies u not in (chat.c).participants
    }
}

/*
when
    OC.acquire[m,c]
require
    some m.host and no m.chat
*/

fact {
    all m : Meeting, c : Chat | always {
        OC.acquire[m,c] implies some m.host and no m.chat
    }
}

/*
when
    OC.release[m,c]
require
    no m.host
*/

fact {
    all m : Meeting, c : Chat | always {
        OC.release[m,c] implies no m.host
    }
}

