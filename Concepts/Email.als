module Concepts/Email[User,Content]
open Action

// State

sig Message {
    from, to : one User,
    content : one Content
}

abstract sig Email extends Concept {
    var inbox : User -> Message,
    var read : User -> Message
}

// Initial state

fact Init {
    no inbox
    no read
}

// Actions

var abstract sig EmailAction extends Action { var u : User, var m : Message } { c in Email }

var sig Send extends EmailAction { } {
    m.from = u
    m not in c.inbox[m.to]
    inbox' = inbox + (c -> m.to -> m)
    read' = read
}

var sig Read extends EmailAction { } {
    m in c.inbox[u]
    m not in c.read[u]
    read' = read + (c -> u -> m)
    inbox' = inbox
}

var sig Delete extends EmailAction { } {
    m in c.inbox[u]
    inbox' = inbox - (c -> u -> m)
    read' = read - (c -> u -> m)
}

fact Stutter {
    always {
        no EmailAction implies {
            inbox' = inbox
            read' = read
        }
    }
}

pred send [e : Email, x : User, y : Message] { some Send and Send.c = e and Send.u = x and Send.m = y }
pred read [e : Email, x : User, y : Message] { some Read and Read.c = e and Read.u = x and Read.m = y }
pred delete [e : Email, x : User, y : Message] { some Delete and Delete.c = e and Delete.u = x and Delete.m = y }

// Properties

check Invariant {
    always {
        // Read messages must be in the inbox
        Email.read in Email.inbox
        // Messages in the inbox must be to the user
        all u : User | Email.inbox[u].to in u
    }
} for 2 but 4 Message, 3 Action, exactly 1 Email expect 0

// Read messages must have been sent
check OP1 {
    always {
        all u : User, m : Message | Email.read[u,m] implies once Email.send[m.from,m]
    }
} for 2 but 4 Message, 3 Action, exactly 1 Email expect 0

// Deleted messages cannot be read again unless resent
check OP2 {
    always {
        all u : User, m : Message | Email.delete[u,m] implies (Email.send[m.from,m] releases not Email.read[u,m])
    }
} for 2 but 4 Message, 3 Action, exactly 1 Email expect 0

// Expected value of inbox
check Inbox {
	all u : User, m : Message | always {
		u->m in Email.inbox iff m.to = u and before {
            not Email.delete[u,m] since Email.send[m.from,m]
        }
	}
} for 2 but 4 Message, 3 Action, exactly 1 Email expect 0

// Expected value of read
check Read {
    all u : User, m : Message | always {
        u->m in Email.read iff before {
            not Email.delete[u,m] since Email.read[u,m]
        }
    }
} for 2 but 4 Message, 3 Action, exactly 1 Email expect 0

// Scenarios

run Scenario1 {
    some u : User {
		all v : User | some m : from.v | eventually Email.read[u,m]
		eventually always no Email.inbox[u]
	}
} for 2 but 4 Message, 3 Action, exactly 3 User, exactly 1 Email expect 1

run Scenario2 {
	some disj u,v : User, m : to.v {
		eventually Email.read[u,m]
	}
} for 2 but 4 Message, 3 Action, exactly 1 Email expect 0
