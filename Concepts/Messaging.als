module Concepts/Messaging[User,Content]
open util/ordering[Time]
open Action

// State

sig Time {}

sig Message {
    from, to : one User,
    content : one Content,
    when : one Time
}

abstract sig Messaging extends Concept {
    var inbox : User -> Message,
    var read : User -> Message,
    var outbox : User -> Message,
    var time : lone Time
}

// Initial state

fact Init {
    no inbox
    no read
    no outbox
    time = Messaging -> first
}

// Actions

var abstract sig MessagingAction extends Action { var u : User, var m : Message } { c in Messaging }

var sig Send extends MessagingAction { } {
    m.from = u
    m.when = c.time
    outbox' = outbox + (c -> u -> m)
    inbox' = inbox + (c -> m.to -> m)
    read' = read
    time' = time - (c -> Time) + (c -> c.time.next)
}

var sig Read extends MessagingAction { } {
    m in c.inbox[u]
    m not in c.read[u]
    read' = read + (c -> u-> m)
    inbox' = inbox
    outbox' = outbox
    time' = time
}

var sig DeleteFromInbox extends MessagingAction { } {
    m in c.inbox[u]
    inbox' = inbox - (c -> u -> m)
    read' = read - (c -> u -> m)
    outbox' = outbox
    time' = time
}

var sig DeleteFromOutbox extends MessagingAction { } {
    m in c.outbox[u]
    outbox' = outbox - (c -> u -> m)
    inbox' = inbox
    read' = read
    time' = time
}


fact Stutter {
    always {
        no MessagingAction implies {
            inbox' = inbox
            read' = read
            outbox' = outbox
            time' = time
        }
    }
}

pred send [e : Messaging, x : User, z : Message] { some Send and Send.c = e and Send.u = x and Send.m = z }
pred read [e : Messaging, x : User, z : Message] { some Read and Read.c = e and Read.u = x and Read.m = z }
pred deleteFromInbox [e : Messaging, x : User, z : Message] { some DeleteFromInbox and DeleteFromInbox.c = e and DeleteFromInbox.u = x and DeleteFromInbox.m = z }
pred deleteFromOutbox [e : Messaging, x : User, z : Message] { some DeleteFromOutbox and DeleteFromOutbox.c = e and DeleteFromOutbox.u = x and DeleteFromOutbox.m = z }

// Properties

check Invariant {
    always {
        // Read messages must be in the inbox
        Messaging.read in Messaging.inbox
        // Messages in a user's inbox must have been sent to that user
        Messaging.inbox.to in iden
        // Messages in a user's outbox must have been sent by that user
        Messaging.outbox.from in iden
    }
} for 3 but 4 Action, exactly 1 Messaging expect 0

// Read messages must have been sent
check OP1 {
    always {
        all u : User, m : Message | Messaging.read[u,m] implies once Messaging.send[m.from,m]
    }
} for 2 but 4 Action, exactly 1 Messaging expect 0

// Deleted messages cannot be read again 
check OP2 {
    always {
        all u : User, m : Message | Messaging.deleteFromInbox[u,m] implies always not Messaging.read[u,m]
    }
} for 2 but 4 Action, exactly 1 Messaging expect 0

// Expected value of inbox
check Inbox {
	always {
		Messaging.inbox = { u : User, m : to.u | before (not Messaging.deleteFromInbox[u,m] since Messaging.send[m.from,m]) }
	}
} for 2 but 4 Action, exactly 1 Messaging expect 0

// Expected value of read
check Read {
    always {
        Messaging.read = { u : User, m : Message | before (not Messaging.deleteFromInbox[u,m] since Messaging.read[u,m]) }
    }
} for 2 but 4 Action, exactly 1 Messaging expect 0

// Expected value of outbox
check Outbox {
    always {
        Messaging.outbox = { u : User, m : Message | before (not Messaging.deleteFromOutbox[u,m] since Messaging.send[u,m]) }
    }
} for 2 but 4 Action, exactly 1 Messaging expect 0

// Scenarios

run Scenario1 {
    some t : User {
		all f : User | some m : from.f | eventually Messaging.read[t,m]
		eventually always no Messaging.inbox[t]
	}
} for 3 but 4 Action, exactly 3 User, exactly 1 Messaging expect 1

run Scenario2 {
	some disj t,f : User, m : to.t {
		Messaging.send[f,m]; Messaging.read[f,m]
	}
} for 2 but 4 Action, exactly 1 Messaging expect 0
