# Messaging

## Specification

```
concept: Messaging[User,Content]
purpose: To allow users to send direct messages to each other.
principle: If a user sends a message, then it can be read by the recipient.
types:
    Message = { to: User, from: User, content: Content, when: Time }
state:
    inbox: User -> set Message
    outbox: User -> set Message
    read: User -> set Message
    time: one Time
actions:
    send(u:User, t:User, m:Content)
        effects: adds {to: t, from: u, content: m, when: time} to the outbox of u and to the inbox of t and time advances
    read(u:User, m:Message)
        requires: m is in the inbox of u
        effects: adds m when time stamp to the read of u
    deleteFromInbox(u:User, m:Message)
        requires: m is in the inbox of u
        effects: removes m from the inbox of u and from the read of u if it is in the read
    deleteFromOutbox(u:User, m:Message)
        requires: m is in the outbox of u
        effects: removes m from the outbox of u
invariants: the messages read by each user are in their inbox, the messages in the outbox are from the user, and the messages in the inbox are to the user, all messages in inboxes and outboxes have a time stamp that is anterior to the current time, there is at most one message in the outbox of each user at any given time, there is at most one message in the inbox of each user at any given time
```

## Formalizations

* [Alloy](Messaging.als)
* [TLA+](Messaging.tla)