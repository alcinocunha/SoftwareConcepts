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

abstract sig MessagingAction extends Action { user : User, message : Message } { concept in Messaging }
sig Send extends MessagingAction {}
fact {
    all x,y : Send | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}
sig Read extends MessagingAction {}
fact {
    all x,y : Read | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}
sig DeleteFromInbox extends MessagingAction {}
fact {
    all x,y : DeleteFromInbox | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}
sig DeleteFromOutbox extends MessagingAction {}
fact {
    all x,y : DeleteFromOutbox | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}

pred send [c : Messaging, u : User, m : Message] {
    m.from = u
    m.when = c.time
    outbox' = outbox + (c -> u -> m)
    inbox' = inbox + (c -> m.to -> m)
    read' = read
    time' = time - (c -> Time) + (c -> c.time.next)

    some a : Send | a.concept = c and a.user = u and a.message = m and occurred' = a
}

pred read [c : Messaging, u : User, m : Message] {
    m in c.inbox[u]
    m not in c.read[u]
    read' = read + (c -> u-> m)
    inbox' = inbox
    outbox' = outbox
    time' = time

    some a : Read | a.concept = c and a.user = u and a.message = m and occurred' = a
}

pred deleteFromInbox [c : Messaging, u : User, m : Message] {
    m in c.inbox[u]
    inbox' = inbox - (c -> u -> m)
    read' = read - (c -> u -> m)
    outbox' = outbox
    time' = time

    some a : DeleteFromInbox | a.concept = c and a.user = u and a.message = m and occurred' = a
}

pred deleteFromOutbox [c : Messaging, u : User, m : Message] {
    m in c.outbox[u]
    outbox' = outbox - (c -> u -> m)
    inbox' = inbox
    read' = read
    time' = time

    some a : DeleteFromOutbox | a.concept = c and a.user = u and a.message = m and occurred' = a
}

pred stutter {
    inbox' = inbox
    read' = read
    outbox' = outbox
    time' = time

    no occurred' & MessagingAction
}

fact Actions {
    always {
        (some c : Messaging, u : User, m : Message | c.send[u,m]) or
        (some c : Messaging, u : User, m : Message | c.read[u,m]) or
        (some c : Messaging, u : User, m : Message | c.deleteFromInbox[u,m]) or
        (some c : Messaging, u : User, m : Message | c.deleteFromOutbox[u,m]) or
        stutter
    }
}

// Properties

check Invariant {
    all c : Messaging | always {
        // Read messages must be in the inbox
        c.read in c.inbox
        // Messages in a user's inbox must have been sent to that user
        c.inbox.to in iden
        // Messages in a user's outbox must have been sent by that user
        c.outbox.from in iden
    }
} for 3 but 10 Action, exactly 1 Messaging expect 0

// Read messages must have been sent
check OP1 {
    all c : Messaging, u : User, m : Message | always {
        c.read[u,m] implies once c.send[m.from,m]
    }
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Deleted messages cannot be read again 
check OP2 {
    all c : Messaging, u : User, m : Message | always {
        c.deleteFromInbox[u,m] implies always not c.read[u,m]
    }
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Expected value of inbox
check Inbox {
	always {
		Messaging.inbox = { u : User, m : to.u | before (not Messaging.deleteFromInbox[u,m] since Messaging.send[m.from,m]) }
	}
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Expected value of read
check Read {
    always {
        Messaging.read = { u : User, m : Message | before (not Messaging.deleteFromInbox[u,m] since Messaging.read[u,m]) }
    }
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Expected value of outbox
check Outbox {
    always {
        Messaging.outbox = { u : User, m : Message | before (not Messaging.deleteFromOutbox[u,m] since Messaging.send[u,m]) }
    }
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Scenarios

run Scenario1 {
    some t : User {
		all f : User | some m : from.f | eventually Messaging.read[t,m]
		eventually always no Messaging.inbox[t]
	}
} for 3 but 10 Action, exactly 3 User, exactly 1 Messaging, 11 steps expect 1

run Scenario2 {
	some disj t,f : User, m : to.t {
		Messaging.send[f,m]; Messaging.read[f,m]
	}
} for 2 but 10 Action, exactly 1 Messaging expect 0
