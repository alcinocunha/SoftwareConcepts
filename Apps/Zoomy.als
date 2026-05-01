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

// The design goal

check Design {
    always {
        no reactions iff {
            host in ~scheduled
            Meeting <: chat in host.User -> one Chat
			joined.Time = ~chat.participants
        }
    }
} for 2 but 12 Action, 6 Reaction, 1 Meeting, 1 Chat, 12 steps expect 0

// The following does not hold but there is no problem because one can only read messages sent after joining
check AcquireNoMessage {
    always {
        all m : Meeting, c : Chat | OC.acquire[m,c] implies no c.sent
    }
} for 1 but 12 Action, 6 Reaction, 1 Meeting, 1 Chat, 12 steps expect 1

check AcquireNoJoined {
    always {
        all m : Meeting, c : Chat | OC.acquire[m,c] implies no c.joined
    }
} for 1 but 12 Action, 6 Reaction, 1 Meeting, 1 Chat, 12 steps expect 0

check SenderIsParticipant {
    always {
        all c : Chat, u : User, m : Content | c.send[u,m] implies u in (chat.c).participants
    }
} for 1 but 12 Action, 5 Reaction, 1 Meeting, 1 Chat, 12 steps expect 0

// Scenarios

run Scenario {
    // Eventually an user sends a message and later the respective meeting ends
    some c : Chat, u : User, m : Content | eventually {
        c.send[u,m]
        eventually (chat.c).end[u]
    }
    eventually always no reactions
} for 2 but 10 Action, 5 Reaction, 1 Meeting, 1 Chat expect 1

// Reactions

/*
reaction start_acquire
when
    m.start[u]
then
    some c : Chat | OC.acquire[m,c]
*/

sig Start_Acquire extends Reaction { meeting : Meeting }
fact {
    all x,y : Start_Acquire | x.meeting = y.meeting implies x = y
}
fact {
    all m : Meeting | always {
        (some r : Start_Acquire & reactions_to_add | r.meeting = m) iff (some u : User | m.start[u])
        (some r : Start_Acquire & reactions_to_remove | r.meeting = m) iff (some c : Chat | OC.acquire[m,c])
    }
}

/*
reaction end_release
when
    m.end[u]
then
    OC.release[m,m.chat]
*/

sig End_Release extends Reaction { meeting : Meeting }
fact {
    all x,y : End_Release | x.meeting = y.meeting implies x = y
}
fact {
    all m : Meeting | always {
        (some r : End_Release & reactions_to_add | r.meeting = m) iff (some u : User | m.end[u])
        (some r : End_Release & reactions_to_remove | r.meeting = m) iff (OC.release[m,m.chat])
    }
}

/*
reaction end_leave
when
    m.end[h]
where
    c in m.chat and u in c.joined.Time
then
    c.leave[u]
*/

sig End_Leave extends Reaction { chat : Chat, user : User }
fact {
    all x,y : End_Leave | x.chat = y.chat and x.user = y.user implies x = y
}
fact {
    all c : Chat, u : User | always {
        (some r : End_Leave & reactions_to_add | r.chat = c and r.user = u) iff (some m : Meeting, h : User | m.end[h] and c in m.chat and u in c.joined.Time)
        (some r : End_Leave & reactions_to_remove | r.chat = c and r.user = u) iff (c.leave[u])
    }
}

/*
reaction join_join
when
    m.join[u]
where
    c in m.chat
then
    c.join[u]
*/

sig Join_Join extends Reaction { chat : Chat, user : User }
fact {
    all x,y : Join_Join | x.chat = y.chat and x.user = y.user implies x = y
}
fact {
    all c : Chat, u : User | always {
        (some r : Join_Join & reactions_to_add | r.chat = c and r.user = u) iff (some m : Meeting | m.join[u] and c in m.chat)
        (some r : Join_Join & reactions_to_remove | r.chat = c and r.user = u) iff (c.join[u])
    }  
}

/*
reaction leave_leave
when
    m.leave[u]
where
    c in m.chat
then
    c.leave[u]
*/

sig Leave_Leave extends Reaction { chat : Chat, user : User }
fact {
    all x,y : Leave_Leave | x.chat = y.chat and x.user = y.user implies x = y
}
fact {
    all c : Chat, u : User | always {
        (some r : Leave_Leave & reactions_to_add | r.chat = c and r.user = u) iff (some m : Meeting | m.leave[u] and c in m.chat)
        (some r : Leave_Leave & reactions_to_remove | r.chat = c and r.user = u) iff (c.leave[u])
    }
}


/*
reaction start_error
when
    m.start[u]
where
    m not in u.scheduled
then
    error
*/

sig Start_Error extends Reaction { }
fact {
    all x,y : Start_Error | x = y
}
fact {
    always {
        (some Start_Error & reactions_to_add) iff (some m : Meeting, u : User | m.start[u] and m not in u.scheduled)
        (some Start_Error & reactions_to_remove) iff error
    }  
}

/*
reaction release_meeting_error
when
    OM.release[u,m]
where
    some m.host
then
    error
*/

sig Release_Meeting_Error extends Reaction { }
fact {
    all x,y : Release_Meeting_Error | x = y
}
fact {
    always {
        (some Release_Meeting_Error & reactions_to_add) iff (some u : User, m : Meeting | OM.release[u,m] and some m.host)
        (some Release_Meeting_Error & reactions_to_remove) iff error
    }
}

/*
reaction join_error
when
    c.join[u]
where
    no (chat.c).host or u not in (chat.c).participants
then
    error
*/

sig Join_Error extends Reaction { }
fact {
    all x,y : Join_Error | x = y
}
fact {
    always {
        (some Join_Error & reactions_to_add) iff (some c : Chat, u : User | c.join[u] and (no (chat.c).host or u not in (chat.c).participants))
        (some Join_Error & reactions_to_remove) iff error
    }
}

/*
reaction leave_error
when
    c.leave[u]
where
    u in (chat.c).participants
then
    error
*/

sig Leave_Error extends Reaction { }
fact {
    all x,y : Leave_Error | x = y
}
fact {
    always {
        (some Leave_Error & reactions_to_add) iff (some c : Chat, u : User | c.leave[u] and u in (chat.c).participants)
        (some Leave_Error & reactions_to_remove) iff error
    }
}

/*
reaction acquire_chat_error
when
    OC.acquire[m,c]
where
    no m.host or some m.chat
then
    error
*/

sig Acquire_Chat_Error extends Reaction { }
fact {
    all x,y : Acquire_Chat_Error | x = y
}
fact {
    always {
        (some Acquire_Chat_Error & reactions_to_add) iff (some m : Meeting, c : Chat | OC.acquire[m,c] and (no m.host or some m.chat))
        (some Acquire_Chat_Error & reactions_to_remove) iff error
    }
}

/*
reaction release_chat_error
when
    OC.release[m,c]
where
    some m.host
then
    error
*/

sig Release_Chat_Error extends Reaction { }
fact {
    all x,y : Release_Chat_Error | x = y
}
fact {
    always {
        (some Release_Chat_Error & reactions_to_add) iff (some m : Meeting, c : Chat | OC.release[m,c] and some m.host)
        (some Release_Chat_Error & reactions_to_remove) iff error
    }
}

