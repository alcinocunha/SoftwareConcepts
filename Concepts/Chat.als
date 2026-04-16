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
var abstract sig ChatAction extends Action { var u : User } { c in Chat }

var sig Join extends ChatAction { } {
    u not in c.joined.Time
    some c.time
    joined' = joined + c->u->c.time
    messages' = messages
    read' = read
    time' = time
}

var sig Leave extends ChatAction { } {
    u in c.joined.Time
    joined' = joined - c->u->Time
    messages' = messages
    read' = read - c->u->Message
    time' = time
}

var sig Send extends ChatAction { var m : Message } {
    u in c.joined.Time
    m.from = u
    m.when = c.time
    messages' = messages + c->m
    joined' = joined
    read' = read + c->u->m
    time' = time - (c -> Time) + (c -> c.time.next)
}

var sig Delete extends ChatAction { var m : Message } {
    u in c.joined.Time
    m in c.messages
    m.from = u
    messages' = messages - c->m
    joined' = joined
    read' = read - c->User->m
    time' = time
}

var sig Read extends ChatAction { var m : Message } {
    u in c.joined.Time
    m in c.messages
    m not in c.read[u]
    gte[m.when, c.joined[u]]
    read' = read + c->u->m
    joined' = joined
    messages' = messages
    time' = time
}

fact Stutter {
    always {
        no ChatAction implies {
            joined' = joined
            messages' = messages
            read' = read
            time' = time
        }
    }
}

pred join [x : Chat, y : User] { some Join and Join.c = x and Join.u = y }
pred leave [x : Chat, y : User] { some Leave and Leave.c = x and Leave.u = y }
pred send [x : Chat, y : User, z : Message] { some Send and Send.c = x and Send.u = y and Send.m = z }
pred delete [x : Chat, y : User, z : Message] { some Delete and Delete.c = x and Delete.u = y and Delete.m = z }
pred read [x : Chat, y : User, z : Message] { some Read and Read.c = x and Read.u = y and Read.m = z }

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
} for 2 but exactly 1 Chat, 5 Action expect 0

// Expected value of joined
check Joined {
    all u : User, t : Time | always {
        u->t in Chat.joined iff before {
            not Chat.leave[u] since (Chat.join[u] and Chat.time = t)
        }
    }
} for 2 but exactly 1 Chat, 5 Action expect 0

// Expected value of messages
check Messages {
    always {
        Chat.messages = { m : Message | before (not Chat.delete[m.from,m] since Chat.send[m.from,m]) }
    }
} for 2 but exactly 1 Chat, 5 Action expect 0

// Expected value of read
check Read {
    all u : User, m : Message | always {
        u->m in Chat.read iff before {
            not (Chat.leave[u] or Chat.delete[m.from,m]) since (Chat.read[u,m] or Chat.send[u,m])
        }
    }
} for 2 but exactly 1 Chat, 5 Action expect 0

// Operational principles

// After a user leaves they cannot read or send messages until they join again
check LeavePreventsReadSend {
    all u : User, m : Message | always {
        Chat.leave[u] implies (Chat.join[u] releases not (Chat.read[u,m] or Chat.send[u,m]))
    }
} for 2 but exactly 1 Chat, 5 Action expect 0

// Scenarios

// Someone reads something
run Scenario1 {
    some u : User, m : Message | eventually Chat.read[u, m]
} for 3 but exactly 1 Chat, 5 Action expect 1
