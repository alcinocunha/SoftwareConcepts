# concept: `Owning[User,Resource]`

* **purpose**: To allow users to own resources.
* **principle**: If a user acquires a resource, it can only be acquired again after it is released.
* **state**:
    * a set of `User`s with
        * an `owns` set of `Resource`s
* **actions**:
    * `acquire(u:User, t:Resource)`
        * **requires**: `t` is not owned by any user
        * **effects**: adds `t` to the `owns` of `u`
    * `release(u:User, t:Resource)`
        * **requires**: `t` is owned by `u`
        * **effects**: removes `t` from the `owns` of `u`
* **invariants**:
    * a resource can only be owned by at most one user at a time
* **formalizations**: [Alloy](Owning.als), [TLA+](Owning.tla)
