# concept: `Messaging[User,Content]`

* **purpose**: To allow users to send direct messages to each other.
* **principle**: If a user sends a message, then it can be read by the recipient.
* **state**:
    * a set of `User`s with
        * an `inbox` set of `Message`s
        * an `outbox` set of `Message`s
        * a `read` set of `Message`s
* **actions**:
    * `send(u:User, m:Message)`
        * **requires**: `u` is the sender of `m`
        * **effects**: adds `m` to the `outbox` of `u` and to the `inbox` of the recipient of `m`
    * `read(u:User, m:Message)`
        * **requires**: `m` is in the `inbox` of `u`
        * **effects**: adds `m` to the `read` of `u`
    * `deleteFromInbox(u:User, m:Message)`
        * **requires**: `m` is in the `inbox` of `u`
        * **effects**: removes `m` from the `inbox` of `u` and from the `read` of `u`
    * `deleteFromOutbox(u:User, m:Message)`
        * **requires**: `m` is in the `outbox` of `u`
        * **effects**: removes `m` from the `outbox` of `u`
* **invariants**:
    * the `inbox` of a user only contains messages sent to that user
    * the `outbox` of a user only contains messages sent by that user
    * the `read` of a user only contains messages that are in the `inbox` of that user
* **formalizations**: [Alloy](Messaging.als)