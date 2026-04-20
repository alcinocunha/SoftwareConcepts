module Concepts/Meeting[User]
open Action

// State

abstract sig Meeting extends Concept {
    var host : set User,
    var participants : set User
}

// Initial state

fact Init {
    no host
    no participants
}

// Actions
abstract sig MeetingAction extends Action { user : User } { concept in Meeting }
sig Start extends MeetingAction {}
fact {
    all x,y : Start | x.concept = y.concept and x.user = y.user implies x = y
}
sig Join extends MeetingAction {}
fact {    
    all x,y : Join | x.concept = y.concept and x.user = y.user implies x = y 
}
sig Leave extends MeetingAction {}
fact {    
    all x,y : Leave | x.concept = y.concept and x.user = y.user implies x = y 
}
sig End extends MeetingAction {}
fact {    
    all x,y : End | x.concept = y.concept and x.user = y.user implies x = y 
}

pred start [c : Meeting, u : User] {
    no c.host
    host' = host + c->u
    participants' = participants

    some a : Start | a.concept = c and a.user = u and occurred' = a
}

pred join [c : Meeting, u : User] {
    some c.host
    u not in c.participants
    participants' = participants + c->u
    host' = host

    some a : Join | a.concept = c and a.user = u and occurred' = a
}

pred leave [c : Meeting, u : User] {
    u in c.participants
    participants' = participants - c->u
    host' = host

    some a : Leave | a.concept = c and a.user = u and occurred' = a
}

pred end [c : Meeting, u : User] {
    u in c.host
    host' = host - c->u
    participants' = participants - c->User

    some a : End | a.concept = c and a.user = u and occurred' = a
}

pred stutter {
    host' = host
    participants' = participants

    no occurred' & MeetingAction
}

fact Actions {
    always {
        (some c : Meeting, u : User | start[c,u]) or
        (some c : Meeting, u : User | join[c,u]) or
        (some c : Meeting, u : User | leave[c,u]) or
        (some c : Meeting, u : User | end[c,u]) or
        stutter
    }
}

// Properties

check Invariant {
    always {
        // At most one host starts a meeting
        lone Meeting.host
        // Meetings with participants have started
        some Meeting.participants implies some Meeting.host
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0

// Expected value of host
check Host {
    all u : User | always {
        u in Meeting.host iff before (not Meeting.end[u] since Meeting.start[u])
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0

// Expected value of participants
check Participants {
    all u : User | always {
        u in Meeting.participants iff before {
            not (Meeting.leave[u] or some h : User | Meeting.end[h]) since Meeting.join[u]
        }
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0

// Operational principles

// After a meeting ends no one can join until it is started again
check EndPreventsJoin {
    all h,u : User | always {
            Meeting.end[h] implies ((some h : User | Meeting.start[h]) releases not Meeting.join[u])
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0

// Leave undoes Join
check LeaveUndoesJoin {
    all u : User | always {
        (Meeting.join[u];Meeting.leave[u]) implies (host'' = host and participants'' = participants)
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0

// End undoes Start
check EndUndoesStart {
    all u : User | always {
        (Meeting.start[u];Meeting.end[u]) implies (host'' = host and participants'' = participants)
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0

// Scenarios

// start; host joins; user joins; end
run Scenario1 {
    some disj h,u : User {
        Meeting.start[h]; Meeting.join[h]; Meeting.join[u]; Meeting.end[h]
    }
} for 3 but exactly 1 Meeting, 10 Action expect 1

// start; end; join
run Scenario2 {
    some disj h,u : User {
        Meeting.start[h]; Meeting.end[h]; Meeting.join[u]
    }
} for 3 but exactly 1 Meeting, 10 Action expect 0
