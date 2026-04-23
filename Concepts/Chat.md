# concept: `Chat[User,Content]`

* **purpose**: To allow users to send messages to each other in a chat room.
* **principle**: If a user sends a message, then it can be read by users who are in the chat room at the time.
* **state**:
    * a set of `User`s with
        * a `joined` `Time` stamp
        * a `read` set of `Message`s
    * a set `messages` of `Message`s sent to the chat room
* **actions**:
    * `join(u:User)`
        * **requires**: `u` is not in the chat room
        * **effects**: sets `joined` of `u` to the current time
    * `leave(u:User)`
        * **requires**: `u` is in the chat room
        * **effects**: removes the `joined` of `u`
    * `send(u:User, c:Content)`
        * **requires**: `u` is in the chat room
        * **effects**: adds a new `Message` with content `c` and sender `u` to `messages` and advances time
    * `read(u:User, m:Message)`
        * **requires**: `u` is in the chat room and `m` is in `messages` and `u` has not yet read `m`
        * **effects**: adds `m` to the `read` of `u`
    * `delete(u:User, m:Message)`
        * **requires**: `u` is in the chat room and `m` is in `messages` and `u` is the sender of `m`
        * **effects**: removes `m` from `messages` and from the `read` of all users
* **invariants**:
    * `joined` contains at most one time stamp for each user
    * the `read` of a user only contains messages that are in `messages`
    * at most one message can be sent at a time
    * users cannot read messages sent before they joined
* **formalizations**: [Alloy](Chat.als), [TLA+](Chat.tla)