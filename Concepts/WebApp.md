# WebApp

## Specification

```
concept: WebApp[User]
purpose: To allow users to register, login, logout and delete their accounts in a web application.
principle: If a user registers, then they can login, and if they login, then they stay logged in until they logout or delete their account.
state:
    registered: set User
    loggedin: lone User
actions:
    register(u:User)
        requires: u is not in registered
        effects: adds u to registered
    login(u:User)
        requires: u is in registered and loggedin is empty
        effects: adds u to loggedin
    logout(u:User)
        requires: u is in loggedin
        effects: removes u from loggedin
    delete(u:User)
        requires: u is in loggedin
        effects: removes u from registered and loggedin
invariants: a logged in user must be registered
```

## Formalizations

* [Alloy](WebApp.als)