module Apps/Zoomy

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

// The app invariant

check Invariant {
    always {
        no Reaction iff {
            host in ~scheduled
            chat in host.User lone -> one Chat
            chat.joined.Time = participants
            no (Chat - Meeting.chat).joined
            no (Chat - Meeting.chat).messages
            no (Chat - Meeting.chat).read
        }
    }
} for 2 but 11 Action, 6 Reaction, 1 Meeting, 2 Chat expect 0

// Scenarios

run Scenario {
    // Eventually an user sends a message and later the respective meeting ends
    some c : Chat, u : User, m : Message | eventually {
        c.send[u,m]
        eventually (chat.c).end[u]
    }
    eventually always no Reaction
} for 2 but 11 Action, 6 Reaction, 1 Meeting, 1 Chat expect 1

// Reactions

/*
reaction StartMeeting[m]
when
    m.start[u]
then
    (some c : Chat | OC.acquire[m,c]) or m.end[u]
*/

var sig StartMeeting extends Reaction { var m : Meeting }
pred StartMeeting [x : Meeting] { some r : StartMeeting | r.m = x }

fact {
    all m : Meeting | always {
        StartMeeting[m] iff some u : User | before {
            not ((some c : Chat | OC.acquire[m,c]) or m.end[u]) since m.start[u]
        }
    }
}

/*
reaction EndMeeting[m]
when
    m.end[u]
where
    c in m.chat
then
    OC.release[m,c]
*/

var sig EndMeeting extends Reaction { var m : Meeting }
pred EndMeeting [x : Meeting] { some r : EndMeeting | r.m = x }

fact {
    all m : Meeting | always {
        EndMeeting[m] iff some u : User, c : Chat | before {
            not OC.release[m,c] since (m.end[u] and c in m.chat)
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
pred EndMeetingForceLeaving [x : Meeting, y : User] { some r : EndMeetingForceLeaving | r.m = x and r.u = y }

fact {
    all m : Meeting, u : User | always {
        EndMeetingForceLeaving[m,u] iff some h : User, c : Chat | before {
            not c.leave[u] since (m.end[h] and c in m.chat and u in c.joined.Time)
        }
    }
}

// There is a potential issue with the following reaction, which might deadlock if the previous one is run first
// because only the sender of a message can delete it.

/*
reaction EndMeetingDeleteMessages[m,t]
when
    m.end[h]
where
    c in m.chat and t in m.chat.messages
then
    c.delete[t.from,t]
*/

var sig EndMeetingDeleteMessages extends Reaction { var m : Meeting, var t : Message }
pred EndMeetingDeleteMessages [x : Meeting, y : Message] { some r : EndMeetingDeleteMessages | r.m = x and r.t = y }

fact {
    all m : Meeting, t : Message | always {
        EndMeetingDeleteMessages[m,t] iff some h : User, c : Chat | before {
            not c.delete[t.from,t] since (m.end[h] and c in m.chat and t in c.messages)
        }
    }
}

/*
reaction JoinMeeting[m,u]
when
    m.join[u]
where
    c in m.chat and u not in c.joined.Time
then
    c.join[u] or m.leave[u] or (some h : User | m.end[h])
*/

var sig JoinMeeting extends Reaction { var m : Meeting, var u : User }
pred JoinMeeting [x : Meeting, y : User] { some r : JoinMeeting | r.m = x and r.u = y }

fact {
    all m : Meeting, u : User | always {
        JoinMeeting[m,u] iff some c : Chat | before {
            not (c.join[u] or m.leave[u] or (some h : User | m.end[h])) since (m.join[u] and c in m.chat and u not in c.joined.Time)
        }
    }
}

/*
reaction LeaveMeeting[m,u]
when
    m.leave[u]
where
    c in m.chat and u in c.joined.Time
then
    c.leave[u] or m.join[u] or (some h : User | m.end[h])
*/

var sig LeaveMeeting extends Reaction { var m : Meeting, var u : User }
pred LeaveMeeting [x : Meeting, y : User] { some r : LeaveMeeting | r.m = x and r.u = y }

fact {
    all m : Meeting, u : User | always {
        LeaveMeeting[m,u] iff some c : Chat | before {
            not (c.leave[u] or m.join[u] or (some h : User | m.end[h])) since (m.leave[u] and c in m.chat and u in c.joined.Time)
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

/*
when
    m.join[u]
require
    some m.chat
*/

fact {
    all m : Meeting, u : User | always {
        m.join[u] implies some m.chat
    }
}

/*
when
    m.start[u]
require
    no m.chat
*/

fact {
    all m : Meeting, u : User | always {
        m.start[u] implies no m.chat
    }
}

/*
when
    c.send[u,m]
require
    some (chat.c).host
*/

fact {
    all c : Chat, u : User, m : Message | always {
        c.send[u,m] implies some (chat.c).host
    }
}
