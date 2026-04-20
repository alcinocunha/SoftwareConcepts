# concept: `Owning[User,Thing]`

* **purpose**: To allow users to own things.
* **principle**: If a user acquires a thing, it can only be acquired again after it is released.
* **state**:
    * a set of `User`s with
        * an `owns` set of `Thing`s
* **actions**:
    * `acquire(u:User, t:Thing)`
        * **requires**: `t` is not owned by any user
        * **effects**: adds `t` to the `owns` of `u`
    * `release(u:User, t:Thing)`
        * **requires**: `t` is owned by `u`
        * **effects**: removes `t` from the `owns` of `u`
* **invariants**:
    * a thing can only be owned by at most one user at a time
* **formalizations**: [Alloy](Owning.als)
