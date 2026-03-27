module Concepts/WebApp[User]
open Action

// State

abstract sig WebApp extends Concept {
    var registered : set User,
    var loggedin : set User
}

// Initial state

fact Init {
    no registered
    no loggedin
}

// Actions

var abstract sig WebAppAction extends Action { var u : User} { c in WebApp }

var sig Register extends WebAppAction { } {
    u not in c.registered
    registered' = registered + c->u
    loggedin' = loggedin
}

var sig Login extends WebAppAction { } {
    no c.loggedin
    u in c.registered
    registered' = registered
    loggedin' = loggedin + c->u
}

var sig Logout extends WebAppAction { } {
    u in c.loggedin
    registered' = registered
    loggedin' = loggedin - c->User
}

var sig Delete extends WebAppAction { } {
    u in c.loggedin
    registered' = registered - c->u
    loggedin' = loggedin - c->u
}

fact Stutter {
    always {
        no WebAppAction implies {
            registered' = registered
            loggedin' = loggedin
        }
    }
}

pred register [a : WebApp, x : User] { some Register and Register.c = a and Register.u = x }
pred login [a : WebApp, x : User] { some Login and Login.c = a and Login.u = x }
pred logout [a : WebApp, x : User] { some Logout and Logout.c = a and Logout.u = x }
pred delete [a : WebApp, x : User] { some Delete and Delete.c = a and Delete.u = x }

// Properties

// Logged in users are registered
check Invariant {
    always loggedin in registered
} for 2 but exactly 1 WebApp, 4 Action expect 0

// After login the user stays logged in until they logout or delete their account
check Principle {
    all u : User | always (WebApp.login[u] implies after ((WebApp.logout[u] or WebApp.delete[u]) releases u in WebApp.loggedin))
} for 2 but exactly 1 WebApp, 4 Action expect 0

// Scenarios

run Scenario1 {
    some disj u,v : User {
        WebApp.register[u]; WebApp.register[v]; WebApp.login[u]; WebApp.logout[u]; WebApp.login[v]; WebApp.delete[v]
    }
} for 2 but exactly 1 WebApp, 4 Action expect 1

run Scenario2 {
    some disj u,v : User {
        WebApp.register[u]; WebApp.register[v]; WebApp.login[u]; WebApp.login[v]
    }
} for 2 but exactly 1 WebApp, 4 Action expect 0