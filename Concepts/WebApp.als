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

abstract sig WebAppAction extends Action { user : User} { concept in WebApp }
sig Register extends WebAppAction {}
fact {
    all x,y : Register | x.concept = y.concept and x.user = y.user implies x = y
}
sig Login extends WebAppAction {}
fact {    
    all x,y : Login | x.concept = y.concept and x.user = y.user implies x = y 
}
sig Logout extends WebAppAction {}
fact {    
    all x,y : Logout | x.concept = y.concept and x.user = y.user implies x = y 
}
sig Delete extends WebAppAction {}
fact {   
    all x,y : Delete | x.concept = y.concept and x.user = y.user implies x = y 
}

pred register [c : WebApp, u : User] {
    u not in c.registered
    registered' = registered + c->u
    loggedin' = loggedin

    some a : Register | a.concept = c and a.user = u and occurred' = a
}

pred login [c : WebApp, u : User] {
    no c.loggedin
    u in c.registered
    registered' = registered
    loggedin' = loggedin + c->u

    some a : Login | a.concept = c and a.user = u and occurred' = a
}

pred logout [c : WebApp, u : User] {
    u in c.loggedin
    registered' = registered
    loggedin' = loggedin - c->u

    some a : Logout | a.concept = c and a.user = u and occurred' = a
}

pred delete [c : WebApp, u : User] {
    u in c.loggedin
    registered' = registered - c->u
    loggedin' = loggedin - c->u

    some a : Delete | a.concept = c and a.user = u and occurred' = a
}

pred stutter {
    registered' = registered
    loggedin' = loggedin

    no occurred' & WebAppAction
}

fact Actions {
    always {
        (some c : WebApp, u : User | c.register[u]) or
        (some c : WebApp, u : User | c.login[u]) or
        (some c : WebApp, u : User | c.logout[u]) or
        (some c : WebApp, u : User | c.delete[u]) or
        stutter
    }
}

// Properties

// Logged in users are registered
check Invariant {
    always {
        lone loggedin
        loggedin in registered
    } 
} for 2 but exactly 1 WebApp, 10 Action expect 0

// After login the user stays logged in until they logout or delete their account
check Principle {
    all u : User | always (WebApp.login[u] implies after ((WebApp.logout[u] or WebApp.delete[u]) releases u in WebApp.loggedin))
} for 2 but exactly 1 WebApp, 10 Action expect 0

// Scenarios

run Scenario1 {
    some disj u,v : User {
        WebApp.register[u]; WebApp.register[v]; WebApp.login[u]; WebApp.logout[u]; WebApp.login[v]; WebApp.delete[v]
    }
} for 2 but exactly 1 WebApp, 10 Action expect 1

run Scenario2 {
    some disj u,v : User {
        WebApp.register[u]; WebApp.register[v]; WebApp.login[u]; WebApp.login[v]
    }
} for 2 but exactly 1 WebApp, 10 Action expect 0
