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
    c.host' = c.host + u
    c.participants' = c.participants

    some a : Start & action | a.concept = c and a.user = u
}

pred join [c : Meeting, u : User] {
    some c.host
    u not in c.participants
    c.participants' = c.participants + u
    c.host' = c.host

    some a : Join & action | a.concept = c and a.user = u
}

pred leave [c : Meeting, u : User] {
    u in c.participants
    c.participants' = c.participants - u
    c.host' = c.host

    some a : Leave & action | a.concept = c and a.user = u
}

pred end [c : Meeting, u : User] {
    u in c.host
    c.host' = c.host - u
    c.participants' = c.participants - User

    some a : End & action | a.concept = c and a.user = u
}

pred stutter[c : Meeting] {
    c.host' = c.host
    c.participants' = c.participants

    no a : action | a.concept = c
}

fact Actions {
    all c : Meeting | always {
        (some u : User | c.start[u]) or
        (some u : User | c.join[u]) or
        (some u : User | c.leave[u]) or
        (some u : User | c.end[u]) or
        c.stutter[]
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
