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

abstract sig Chat extends Concept {
    var joined : User -> Time,
    var messages : set Message,
    var read : User -> Message,
    var time : lone Time
}

// Initial state
fact Init {
    no joined
    no messages
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
sig Send extends ChatAction { message : Message }
fact {
    all x,y : Send | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
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
    some c.time
    c.joined' = c.joined + u->c.time
    c.messages' = c.messages
    c.read' = c.read
    c.time' = c.time

    some a : Join & action | a.concept = c and a.user = u
}

pred leave [c : Chat, u : User] {
    u in c.joined.Time
    c.joined' = c.joined - u->Time
    c.messages' = c.messages
    c.read' = c.read - u->Message
    c.time' = c.time

    some a : Leave & action | a.concept = c and a.user = u
}

pred send [c : Chat, u : User, m : Message] {
    u in c.joined.Time
    m.from = u
    m.when = c.time
    c.messages' = c.messages + m
    c.joined' = c.joined
    c.read' = c.read + u->m
    c.time' = c.time.next

    some a : Send & action | a.concept = c and a.user = u and a.message = m
}

pred delete [c : Chat, u : User, m : Message] {
    u in c.joined.Time
    m in c.messages
    m.from = u
    c.messages' = c.messages - m
    c.joined' = c.joined
    c.read' = c.read - User->m
    c.time' = c.time

    some a : Delete & action | a.concept = c and a.user = u and a.message = m
}

pred read [c : Chat, u : User, m : Message] {
    u in c.joined.Time
    m in c.messages
    m not in c.read[u]
    gte[m.when, c.joined[u]]
    c.read' = c.read + u->m
    c.joined' = c.joined
    c.messages' = c.messages
    c.time' = c.time

    some a : Read & action | a.concept = c and a.user = u and a.message = m
}

pred stutter [c : Chat] {
    c.joined' = c.joined
    c.messages' = c.messages
    c.read' = c.read
    c.time' = c.time

    no a : action | a.concept = c
}

fact Actions {
    all c : Chat | always {
        (some u : User | c.join[u]) or
        (some u : User | c.leave[u]) or
        (some u : User, m : Message | c.send[u,m]) or
        (some u : User, m : Message | c.delete[u,m]) or
        (some u : User, m : Message | c.read[u,m]) or
        c.stutter[]
    }
}

// Properties

check Invariant {
    always {
        // No double joins
        all u : User | lone Chat.joined[u]
        // At most one message was sent at a time
        all disj m1, m2 : Chat.messages | m1.when != m2.when
        // Read messages must be in the chat
        Chat.read[User] in Chat.messages
        // Users cannot read messages sent before they joined
        all u : User, m : Chat.read[u] | gte[m.when, Chat.joined[u]]
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Expected value of joined
check Joined {
    all u : User, t : Time | always {
        u->t in Chat.joined iff before {
            not Chat.leave[u] since (Chat.join[u] and Chat.time = t)
        }
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Expected value of messages
check Messages {
    always {
        Chat.messages = { m : Message | before (not Chat.delete[m.from,m] since Chat.send[m.from,m]) }
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Expected value of read
check Read {
    all u : User, m : Message | always {
        u->m in Chat.read iff before {
            not (Chat.leave[u] or Chat.delete[m.from,m]) since (Chat.read[u,m] or Chat.send[u,m])
        }
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Operational principles

// After a user leaves they cannot read or send messages until they join again
check LeavePreventsReadSend {
    all u : User, m : Message | always {
        Chat.leave[u] implies (Chat.join[u] releases not (Chat.read[u,m] or Chat.send[u,m]))
    }
} for 2 but exactly 1 Chat, 10 Action expect 0

// Scenarios

// Someone reads something and everyone leaves the chat
run Scenario1 {
    some u : User, m : Message | eventually Chat.read[u, m]
	eventually always no joined
} for 3 but exactly 1 Chat, 10 Action expect 1
