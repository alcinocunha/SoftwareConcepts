# app: `OnlineDrive`

* **types**:
    * a set of `User`s
    * a set of `File`s
* **concepts**:
    * one `WebApp[User]` named `A`
    * one `Owning[User,Trash]` named `O`
    * a set of `Trash[File]`
* **views**:
    * `trash` = `O.owns`
* **invariants**:
    * every registered user owns exactly one trash and unregistered users do not own any trash
    * the content of a `Trash` is the one that results from actions of the owning `User`, unless it is acquired by another user, in which case it must be empty.
* **reactions**:
```
reaction register_acquire
when
    A.register[u]
then
    some t : Trash | O.acquire[u,t]

reaction delete_release
when
    A.delete[u]
then
    O.release[u,u.trash]

reaction acquire_error
when
    O.acquire[u,t]
where
    u not in registered or some u.trash or some t.accessible or some t.trashed
then
    error

reaction release_error
when
    O.release[u,t]
where
    u in registered
then
    error

reaction create_error
when
    t.create[f]
where
    t != loggedin.trash
then
    error

reaction delete_error
when
    t.delete[f]
where
    t != loggedin.trash
then
    error

reaction restore_error
when
    t.restore[f]
where
    t != loggedin.trash
then
    error

reaction empty_error
when
    t.empty[]
where
    t != loggedin.trash
then
    error
```
* **formalizations**: [Alloy](OnlineDrive.als)