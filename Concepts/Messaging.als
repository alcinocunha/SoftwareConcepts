module Concepts/Messaging[User,Content]
open Action

// State

sig Message {
    content : one Content
}

abstract sig Messaging extends Concept {
    var inbox : User -> User -> Message,
    var read : User -> User -> Message
}

// Initial state

fact Init {
    no inbox
    no read
}

// Actions

var abstract sig MessagingAction extends Action { var t,f : User, var m : Message } { c in Messaging }

var sig Send extends MessagingAction { } {
    m not in c.inbox[t][f]
    inbox' = inbox + (c -> t -> f -> m)
    read' = read
}

var sig Read extends MessagingAction { } {
    m in c.inbox[t][f]
    m not in c.read[t][f]
    read' = read + (c -> t -> f -> m)
    inbox' = inbox
}

var sig Delete extends MessagingAction { } {
    m in c.inbox[t][f]
    inbox' = inbox - (c -> t -> f -> m)
    read' = read - (c -> t -> f -> m)
}

fact Stutter {
    always {
        no MessagingAction implies {
            inbox' = inbox
            read' = read
        }
    }
}

pred send [e : Messaging, x,y : User, z : Message] { some Send and Send.c = e and Send.f = x and Send.t = y and Send.m = z }
pred read [e : Messaging, x,y : User, z : Message] { some Read and Read.c = e and Read.t = x and Read.f = y and Read.m = z }
pred delete [e : Messaging, x,y : User, z : Message] { some Delete and Delete.c = e and Delete.t = x and Delete.f = y and Delete.m = z }

// Properties

check Invariant {
    always {
        // Read messages must be in the inbox
        Messaging.read in Messaging.inbox
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Read messages must have been sent
check OP1 {
    always {
        all t,f : User, m : Message | Messaging.read[t,f,m] implies once Messaging.send[f,t,m]
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Deleted messages cannot be read again unless resent
check OP2 {
    always {
        all t,f : User, m : Message | Messaging.delete[t,f,m] implies (Messaging.send[f,t,m] releases not Messaging.read[t,f,m])
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Expected value of inbox
check Inbox {
	all t,f : User, m : Message | always {
		t->f->m in Messaging.inbox iff before {
            not Messaging.delete[t,f,m] since Messaging.send[f,t,m]
        }
	}
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Expected value of read
check Read {
    all t,f : User, m : Message | always {
        t->f->m in Messaging.read iff before {
            not Messaging.delete[t,f,m] since Messaging.read[t,f,m]
        }
    }
} for 2 but 3 Action, exactly 1 Messaging expect 0

// Scenarios

run Scenario1 {
    some t : User {
		all f : User | some m : Message | eventually Messaging.read[t,f,m]
		eventually always no Messaging.inbox[t]
	}
} for 2 but 3 Action, exactly 3 User, exactly 1 Messaging expect 1

run Scenario2 {
	some disj t,f : User, m : Message {
		Messaging.send[f,t,m]; Messaging.read[f,t,m]
	}
} for 2 but 3 Action, exactly 1 Messaging expect 0
