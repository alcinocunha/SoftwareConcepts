# concept: `WebApp[User]`

* **purpose**: To allow users to register, login, logout and delete their accounts in a web application.
* **principle**: If a user registers, then they can login, and if they login, then they stay logged in until they logout or delete their account.
* **state**:
    * a `registered` set of `User`s
    * a `loggedin` set of `User`s
* **actions**:
    * `register(u:User)`
        * **requires**: `u` is not in `registered`
        * **effects**: adds `u` to `registered`
    * `login(u:User)`
        * **requires**: `u` is in `registered` and no one is`loggedin`
        * **effects**: adds `u` to `loggedin`
    * `logout(u:User)`
        * **requires**: `u` is in `loggedin`
        * **effects**: removes `u` from `loggedin`
    * `delete(u:User)`
        * **requires**: `u` is in `loggedin`
        * **effects**: removes `u` from `registered` and `loggedin`
* **invariants**:
    * at most one user can be logged in at a time
    * a logged in user must be registered
* **formalizations**: [Alloy](WebApp.als)