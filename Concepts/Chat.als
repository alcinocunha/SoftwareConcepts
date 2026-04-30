module Concepts/Chat[User,Content]
open util/ordering[Time]
open Action

// State

sig Time {}

sig Message {
    from : one User,
    content : one Content,
    when : one Time
}
fact {
    all x,y : Message | x.from = y.from and x.content = y.content and x.when = y.when implies x = y
}

abstract sig Chat extends Concept {
    var joined : User -> lone Time,
    var sent : set Message,
    var read : User -> Message,
    var time : one Time
}

// Initial state
fact Init {
    no joined
    no sent
    no read
    time = Chat->first
}

// Actions
abstract sig ChatAction extends Action { user : User } { concept in Chat }
sig Join extends ChatAction {}
fact {
    all x,y : Join | x.concept = y.concept and x.user = y.user implies x = y
}
sig Leave extends ChatAction {}
fact {
    all x,y : Leave | x.concept = y.concept and x.user = y.user implies x = y
}
sig Send extends ChatAction { content : Content }
fact {
    all x,y : Send | x.concept = y.concept and x.user = y.user and x.content = y.content implies x = y
}
sig Delete extends ChatAction { message : Message }
fact {
    all x,y : Delete | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}
sig Read extends ChatAction { message : Message }
fact {
    all x,y : Read | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}

pred join [c : Chat, u : User] {
    u not in c.joined.Time
    c.joined' = c.joined + u->c.time
    c.sent' = c.sent
    c.read' = c.read
    c.time' = c.time

    some a : Join & action | a.concept = c and a.user = u
}

pred leave [c : Chat, u : User] {
    u in c.joined.Time
    c.joined' = c.joined - u->Time
    c.sent' = c.sent
    c.read' = c.read - u->Message
    c.time' = c.time

    some a : Leave & action | a.concept = c and a.user = u
}

pred send [c : Chat, u : User, x : Content] {
    u in c.joined.Time
    some c.time.next
    some m : Message {
        m.content = x
        m.from = u
        m.when = c.time
        c.sent' = c.sent + m
        c.joined' = c.joined
        c.read' = c.read + u->m
        c.time' = c.time.next
    }
    some a : Send & action | a.concept = c and a.user = u and a.content = x
}

pred delete [c : Chat, u : User, m : Message] {
    u in c.joined.Time
    m in c.sent
    m.from = u
    c.sent' = c.sent - m
    c.joined' = c.joined
    c.read' = c.read - User->m
    c.time' = c.time

    some a : Delete & action | a.concept = c and a.user = u and a.message = m
}

pred read [c : Chat, u : User, m : Message] {
    u in c.joined.Time
    m in c.sent
    m not in c.read[u]
    gte[m.when, c.joined[u]]
    c.read' = c.read + u->m
    c.joined' = c.joined
    c.sent' = c.sent
    c.time' = c.time

    some a : Read & action | a.concept = c and a.user = u and a.message = m
}

pred stutter [c : Chat] {
    c.joined' = c.joined
    c.sent' = c.sent
    c.read' = c.read
    c.time' = c.time

    no a : action | a.concept = c
}

fact Actions {
    all c : Chat | always {
        (some u : User | c.join[u]) or
        (some u : User | c.leave[u]) or
        (some u : User, x : Content | c.send[u,x]) or
        (some u : User, m : Message | c.delete[u,m]) or
        (some u : User, m : Message | c.read[u,m]) or
        c.stutter[]
    }
}

// Properties

check Invariant {
    all c : Chat | always {
        // The messages read by each user are in sent
        c.read[User] in c.sent
        
        // There is at most one message in sent at with a given time stamp
        all disj m1, m2 : c.sent | m1.when != m2.when
        
        // The time stamp of the messages read by an user is posterior to the time of joining the chat room
        all u : User, m : c.read[u] | gte[m.when, c.joined[u]]
        
        // All sent messages have a time stamp that is strictly anterior to the current time
        all m : c.sent | lt[m.when, c.time]

        // All joining time stamps are anterior to the current time
        all u : User | lte[c.joined[u], c.time]
    }
} for 2 but 3 Time, exactly 1 Chat, 10 Action expect 0

// Expected value of joined
check Joined {
    all c : Chat | always {
        c.joined = { u : User, t : Time | before (not c.leave[u] since (c.join[u] and c.time = t)) }
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Expected value of sent
check Sent {
    all c : Chat | always {
        c.sent = { m : Message | before (not c.delete[m.from,m] since (c.send[m.from,m.content] and c.time = m.when)) }
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Expected value of read
check Read {
    all c : Chat | always {
        c.read = { u : User, m : Message | before (not (c.leave[u] or c.delete[m.from,m]) since (c.read[u,m] or (u = m.from and c.send[u,m.content] and c.time = m.when))) }
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Operational principles

// After a user leaves they cannot read or send messages until they join again
check LeavePreventsReadSend {
    all c : Chat, u : User, m : Message, x : Content | always {
        c.leave[u] implies (c.join[u] releases not (c.read[u,m] or c.send[u,x]))
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Scenarios

// Someone reads something and everyone leaves the chat
run Scenario1 {
    some c : Chat, u : User, m : Message {
        eventually c.read[u, m]
	    eventually always no c.joined
    }
} for 3 but exactly 1 Chat, 10 Action expect 1
