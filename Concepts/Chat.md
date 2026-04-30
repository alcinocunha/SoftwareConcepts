# Chat

## Specification

```
concept: Chat[User,Content]
purpose: To allow users to send messages to each other in a chat room.
principle: If a user sends a message, then it can be read by users who are in the chat room at the time.
types:
    Message = { from: User, content: Content, when: Time }
state:
    joined: User -> lone Time
    sent: set Message
    read: User -> set Message
    time: one Time
actions:
    join(u:User)
        requires: u has not joined the chat room at any time
        effects: adds u to joined with the current time
    leave(u:User)
        requires: u has joined the chat room at some time
        effects: removes u from joined
    send(u:User, c:Content)
        requires: u has joined the chat room at some time
        effects: adds {from: u, content: c, when: time} to sent and time advances
    read(u:User, m:Message)
        requires: u has joined the chat room at some time and m is in sent and u has not yet read m
        effects: adds m to the read messages of u
    delete(u:User, m:Message)
        requires: u has joined the chat room at some time and m is in sent and u is the sender of m
        effects: removes m from sent and from the read of all users
invariants: the messages read by each user are in sent, there is at most one message in sent at with a given time stamp, the time stamp of the messages read by an user is posterior to the time of joining the chat room, all sent messages have a time stamp that is strictly anterior to the current time, all joining time stamps are anterior to the current time
```

## Formalizations

* [Alloy](Chat.als)
* [TLA+](Chat.tla)