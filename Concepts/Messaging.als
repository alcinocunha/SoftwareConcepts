module Concepts/Messaging[User,Content]
open Action

// State

sig Message {
    from, to : one User,
    content : one Content
}

abstract sig Messaging extends Concept {
    var inbox : User -> Message,
    var read : User -> Message,
    var sent : set Message
}

// Initial state

fact Init {
    no inbox
    no read
    no sent
}

// Actions

var abstract sig MessagingAction extends Action { var u : User, var m : Message } { c in Messaging }

var sig Send extends MessagingAction { } {
    m.from = u
    m not in c.sent
    sent' = sent + c->m
    inbox' = inbox + (c -> m.to -> m)
    read' = read
}

var sig Read extends MessagingAction { } {
    m in c.inbox[u]
    m not in c.read[u]
    read' = read + (c -> u-> m)
    inbox' = inbox
    sent' = sent
}

var sig Delete extends MessagingAction { } {
    m in c.inbox[u]
    inbox' = inbox - (c -> u -> m)
    read' = read - (c -> u -> m)
    sent' = sent
}

fact Stutter {
    always {
        no MessagingAction implies {
            inbox' = inbox
            read' = read
            sent' = sent
        }
    }
}

pred send [e : Messaging, x : User, z : Message] { some Send and Send.c = e and Send.u = x and Send.m = z }
pred read [e : Messaging, x : User, z : Message] { some Read and Read.c = e and Read.u = x and Read.m = z }
pred delete [e : Messaging, x : User, z : Message] { some Delete and Delete.c = e and Delete.u = x and Delete.m = z }

// Properties

check Invariant {
    always {
        // Messages in the inbox must have been sent
        Messaging.inbox[User] in Messaging.sent
        // Read messages must be in the inbox
        Messaging.read in Messaging.inbox
        // Messages in a user's inbox must have been sent to that user
        Messaging.inbox.to in iden
    }
} for 3 but 3 Action, exactly 1 Messaging expect 0

// Read messages must have been sent
check OP1 {
    always {
        all u : User, m : Message | Messaging.read[u,m] implies once Messaging.send[m.from,m]
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Deleted messages cannot be read again 
check OP2 {
    always {
        all u : User, m : Message | Messaging.delete[u,m] implies always not Messaging.read[u,m]
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Expected value of inbox
check Inbox {
	all u : User, m : Message | always {
		u->m in Messaging.inbox iff m.to = u and before {
            not Messaging.delete[u,m] since Messaging.send[m.from,m]
        }
	}
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Expected value of read
check Read {
    all u : User, m : Message | always {
        u->m in Messaging.read iff before {
            not Messaging.delete[u,m] since Messaging.read[u,m]
        }
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Expected value of sent
check Sent {
    all m : Message | always {
        m in Messaging.sent iff before once Messaging.send[m.from,m]
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Scenarios

run Scenario1 {
    some t : User {
		all f : User | some m : from.f | eventually Messaging.read[t,m]
		eventually always no Messaging.inbox[t]
	}
} for 3 but 3 Action, exactly 3 User, exactly 1 Messaging expect 1

run Scenario2 {
	some disj t,f : User, m : to.t {
		Messaging.send[f,m]; Messaging.read[f,m]
	}
} for 2 but 3 Action, exactly 1 Messaging expect 0
