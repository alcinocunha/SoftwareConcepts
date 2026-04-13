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
var abstract sig MeetingAction extends Action { var u : User } { c in Meeting }

var sig Start extends MeetingAction { } {
    no c.host
    host' = host + c->u
    participants' = participants
}

var sig Join extends MeetingAction { } {
    some c.host
    u not in c.participants
    participants' = participants + c->u
    host' = host
}

var sig Leave extends MeetingAction { } {
    u in c.participants
    participants' = participants - c->u
    host' = host
}

var sig End extends MeetingAction { } {
    u = c.host
    participants' = participants - c->User
    host' = host - c->u
}

fact Stutter {
    always {
        no MeetingAction implies {
            participants' = participants
            host' = host
        }
    }
}

pred start [z : Meeting, y : User] { some Start and Start.c = z and Start.u = y }
pred join [z : Meeting, y : User] { some Join and Join.c = z and Join.u = y }
pred leave [z : Meeting, y : User] { some Leave and Leave.c = z and Leave.u = y }
pred end [z : Meeting, y : User] { some End and End.c = z and End.u = y }

// Properties

check Invariant {
    always {
        // At most one host starts a meeting
        lone Meeting.host
        // Meetings with participants have started
        some Meeting.participants implies some Meeting.host
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0

// Expected value of host
check Host {
    all u : User | always {
        u in Meeting.host iff before (not Meeting.end[u] since Meeting.start[u])
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0

// Expected value of participants
check Participants {
    all u : User | always {
        u in Meeting.participants iff before {
            not (Meeting.leave[u] or some h : User | Meeting.end[h]) since Meeting.join[u]
        }
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0

// Operational principles

// After a meeting ends no one can join until it is started again
check EndPreventsJoin {
    all h,u : User | always {
            Meeting.end[h] implies ((some h : User | Meeting.start[h]) releases not Meeting.join[u])
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0

// Leave undoes Join
check LeaveUndoesJoin {
    all u : User | always {
        (Meeting.join[u];Meeting.leave[u]) implies (host'' = host and participants'' = participants)
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0

// End undoes Start
check EndUndoesStart {
    all u : User | always {
        (Meeting.start[u];Meeting.end[u]) implies (host'' = host and participants'' = participants)
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0

// Scenarios

// start; host joins; user joins; end
run Scenario1 {
    some disj h,u : User {
        Meeting.start[h]; Meeting.join[h]; Meeting.join[u]; Meeting.end[h]
    }
} for 3 but exactly 1 Meeting, 4 Action expect 1

// start; end; join
run Scenario2 {
    some disj h,u : User {
        Meeting.start[h]; Meeting.end[h]; Meeting.join[u]
    }
} for 3 but exactly 1 Meeting, 4 Action expect 0
