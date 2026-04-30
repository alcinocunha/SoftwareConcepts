# concept: `Meeting[User]`

* **purpose**: To allow users to have meetings with each other.
* **principle**: If a user starts a meeting, then they are the host of the meeting until they end it, and if a user joins a meeting, then they are a participant of the meeting until they leave it or the meeting ends.
* **state**:
    * a `host` with at most one `User`
    * a `participants` set of `User`s
* **actions**:
    * `start(u:User)`
        * **requires**: `u` is not the host
        * **effects**: sets `u` as the host
    * `join(u:User)`
        * **requires**: the meeting has a host and `u` is not a participant
        * **effects**: adds `u` to the participants
    * `leave(u:User)`
        * **requires**: `u` is a participant
        * **effects**: removes `u` from the participants
    * `end(u:User)`
        * **requires**: `u` is the host
        * **effects**: removes `u` as the host and removes all participants
* **invariants**:
    * at most one user can be the host of the meeting
    * if there is a host, then there are participants
* **formalizations**: [Alloy](Meeting.als), [TLA+](Meeting.tla)