module Concepts/Meeting[User,Id]
open Action

// State

abstract sig Meeting extends Concept {
    var host : Id -> User,
    var participants : Id -> User,
    var started : set Id
}

// Initial state

fact Init {
    no host
    no participants
    no started
}

// Actions
var abstract sig MeetingAction extends Action { var m : Id, var u : User } { c in Meeting }

var sig Create extends MeetingAction { } {
    m not in c.host.User
    host' = host + c->m->u
    participants' = participants
    started' = started
}

var sig Start extends MeetingAction { } {
    m in c.host.u
    m not in c.started
    started' = started + c->m
    host' = host
    participants' = participants
}

var sig Join extends MeetingAction { } {
    m in c.started
    u not in c.participants[m]
    participants' = participants + c->m->u
    host' = host
    started' = started
}

var sig Leave extends MeetingAction { } {
    u in c.participants[m]
    participants' = participants - c->m->u
    host' = host
    started' = started
}

var sig End extends MeetingAction { } {
    m in c.host.u
    m in c.started
    host' = host
    participants' = participants - c->m->User
    started' = started - c->m
}

fact Stutter {
    always {
        no MeetingAction implies {
            host' = host
            participants' = participants
            started' = started
        }
    }
}

pred create [z : Meeting, x : Id, y : User] { some Create and Create.c = z and Create.m = x and Create.u = y }
pred start [z : Meeting, x : Id, y : User] { some Start and Start.c = z and Start.m = x and Start.u = y }
pred join [z : Meeting, x : Id, y : User] { some Join and Join.c = z and Join.m = x and Join.u = y }
pred leave [z : Meeting, x : Id, y : User] { some Leave and Leave.c = z and Leave.m = x and Leave.u = y }
pred end [z : Meeting, x : Id, y : User] { some End and End.c = z and End.m = x and End.u = y }

// Properties

check Invariant {
    always {
        Meeting.(started + participants.User) in Meeting.host.User
        all m : Id | some Meeting.participants[m] implies m in Meeting.started
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// Expected value of host
check Host {
    all m : Id, u : User | always {
        m in Meeting.host.u iff before once Meeting.create[m,u]
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// Expected value of started
check Started {
    all m : Id | always {
        m in Meeting.started iff before {
            not (some h : User | Meeting.end[m,h]) since (some h : User | Meeting.start[m,h])
        }
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// Expected value of participants
check Participants {
    all m : Id, u : User | always {
        m->u in Meeting.participants iff before {
            not (Meeting.leave[m,u] or some h : User | Meeting.end[m,h]) since Meeting.join[m,u]
        }
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// Operational principles

// A meeting cannot start without being created
check StartRequiresCreate {
    all m : Id, u : User | Meeting.create[m,u] releases not Meeting.start[m,u]
} for 3 but exactly 1 Meeting, 5 Action expect 0

// After a meeting ends no one can join until it is started again
check EndPreventsJoin {
    all m : Id, h,u : User | always {
            Meeting.end[m,h] implies (Meeting.start[m,h] releases not Meeting.join[m,u])
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// Leave undoes Join
check LeaveUndoesJoin {
    all m : Id, u : User | always {
        (Meeting.join[m,u];Meeting.leave[m,u]) implies (host'' = host and participants'' = participants and started'' = started)
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// End undoes Start
check EndUndoesStart {
    all m : Id, u : User | always {
        (Meeting.start[m,u];Meeting.end[m,u]) implies (host'' = host and participants'' = participants and started'' = started)
    }
} for 3 but exactly 1 Meeting, 5 Action expect 0

// Scenarios

// Create; start; host join; user join; end
run Scenario1 {
    some disj h,u : User, i : Id {
        Meeting.create[i,h]; Meeting.start[i,h]; Meeting.join[i,h]; Meeting.join[i,u]; Meeting.end[i,h]
    }
} for 3 but exactly 1 Meeting, 5 Action expect 1
