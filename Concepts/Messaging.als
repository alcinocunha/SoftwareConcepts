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
fact {
    all x,y : Message | x.from = y.from and x.to = y.to and x.content = y.content and x.when = y.when implies x = y
}

abstract sig Messaging extends Concept {
    var inbox : User -> Message,
    var read : User -> Message,
    var outbox : User -> Message,
    var time : one Time
}

// Initial state

fact Init {
    no inbox
    no read
    no outbox
    time = Messaging -> first
}

// Actions

abstract sig MessagingAction extends Action { user : User } { concept in Messaging }
sig Send extends MessagingAction { to : User, content : Content }
fact {
    all x,y : Send | x.concept = y.concept and x.user = y.user and x.to = y.to and x.content = y.content implies x = y
}
sig Read extends MessagingAction { message : Message }
fact {
    all x,y : Read | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}
sig DeleteFromInbox extends MessagingAction {message : Message }
fact {
    all x,y : DeleteFromInbox | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}
sig DeleteFromOutbox extends MessagingAction { message : Message }
fact {
    all x,y : DeleteFromOutbox | x.concept = y.concept and x.user = y.user and x.message = y.message implies x = y
}

pred send [c : Messaging, u : User, t : User, x : Content] {
    some c.time.next
    some m : Message {
        m.from = u
        m.to = t
        m.content = x
        m.when = c.time
        c.outbox' = c.outbox + (u -> m)
        c.inbox' = c.inbox + (m.to -> m)
        c.read' = c.read
        c.time' = c.time.next
    }

    some a : Send & action | a.concept = c and a.user = u and a.to = t and a.content = x
}

pred read [c : Messaging, u : User, m : Message] {
    m in c.inbox[u]
    m not in c.read[u]
    c.read' = c.read + (u -> m)
    c.inbox' = c.inbox
    c.outbox' = c.outbox
    c.time' = c.time

    some a : Read & action | a.concept = c and a.user = u and a.message = m
}

pred deleteFromInbox [c : Messaging, u : User, m : Message] {
    m in c.inbox[u]
    c.inbox' = c.inbox - (u -> m)
    c.read' = c.read - (u -> m)
    c.outbox' = c.outbox
    c.time' = c.time

    some a : DeleteFromInbox & action | a.concept = c and a.user = u and a.message = m
}

pred deleteFromOutbox [c : Messaging, u : User, m : Message] {
    m in c.outbox[u]
    c.outbox' = c.outbox - (u -> m)
    c.inbox' = c.inbox
    c.read' = c.read
    c.time' = c.time

    some a : DeleteFromOutbox & action | a.concept = c and a.user = u and a.message = m
}

pred stutter [c : Messaging] {
    c.inbox' = c.inbox
    c.read' = c.read
    c.outbox' = c.outbox
    c.time' = c.time

    no a : action | a.concept = c
}

fact Actions {
    all c : Messaging | always {
        (some u : User, t : User, x : Content | c.send[u,t,x]) or
        (some u : User, m : Message | c.read[u,m]) or
        (some u : User, m : Message | c.deleteFromInbox[u,m]) or
        (some u : User, m : Message | c.deleteFromOutbox[u,m]) or
        stutter[c]
    }
}

// Properties

check Invariant {
    all c : Messaging | always {
        // The messages read by each user are in their inbox
        c.read in c.inbox

        // The messages in the outbox are from the user
        c.outbox.from in iden

        // The messages in the inbox are to the user
        c.inbox.to in iden

        // All messages in inboxes and outboxes have a time stamp that is strictly anterior to the current time
        all m : c.(outbox+inbox)[User] | lt[m.when, c.time]
        
        // There is at most one message in the outbox of each user with a given time stamp
        all u : User, t : Time | lone c.outbox[u] & when.t

        // There is at most one message in the inbox of each user with a given time stamp
        all u : User, t : Time | lone c.inbox[u] & when.t        
    }
} for 3 but 10 Action, exactly 1 Messaging expect 0

// Read messages must have been sent
check OP1 {
    all c : Messaging, u : User, m : Message | always {
        c.read[u,m] implies once c.send[m.from,m.to,m.content]
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
	all c : Messaging | always {
		c.inbox = { u : User, m : Message | before (not c.deleteFromInbox[u,m] since (m.to = u and c.send[m.from,m.to,m.content] and m.when = c.time)) }
	}
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Expected value of read
check Read {
    all c : Messaging | always {
        c.read = { u : User, m : Message | before (not c.deleteFromInbox[u,m] since c.read[u,m]) }
    }
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Expected value of outbox
check Outbox {
    all c : Messaging | always {
        c.outbox = { u : User, m : Message | before (not c.deleteFromOutbox[u,m] since (m.from = u and c.send[m.from,m.to,m.content] and m.when = c.time)) }
    }
} for 2 but 10 Action, exactly 1 Messaging expect 0

// Scenarios

run Scenario1 {
    some c : Messaging, t : User {
		all f : User | some m : from.f | eventually c.read[t,m]
		eventually always no c.inbox[t]
	}
} for 3 but 10 Action, exactly 3 User, 4 Time, exactly 1 Messaging expect 1

run Scenario2 {
	some c : Messaging, u : User, m : Message {
		m.to != u and c.send[u,m.to,m.content]; c.read[u,m]
	}
} for 2 but 10 Action, exactly 1 Messaging expect 0
