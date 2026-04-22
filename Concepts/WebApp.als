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
    c.registered' = c.registered + u
    c.loggedin' = c.loggedin

    some a : Register & action | a.concept = c and a.user = u
}

pred login [c : WebApp, u : User] {
    no c.loggedin
    u in c.registered
    c.registered' = c.registered
    c.loggedin' = c.loggedin + u

    some a : Login & action | a.concept = c and a.user = u
}

pred logout [c : WebApp, u : User] {
    u in c.loggedin
    c.registered' = c.registered
    c.loggedin' = c.loggedin - u

    some a : Logout & action | a.concept = c and a.user = u
}

pred delete [c : WebApp, u : User] {
    u in c.loggedin
    c.registered' = c.registered - u
    c.loggedin' = c.loggedin - u

    some a : Delete & action | a.concept = c and a.user = u
}

pred stutter[c : WebApp] {
    c.registered' = c.registered
    c.loggedin' = c.loggedin

    no a : action | a.concept = c
}

fact Actions {
    all c : WebApp | always {
        (some u : User | c.register[u]) or
        (some u : User | c.login[u]) or
        (some u : User | c.logout[u]) or
        (some u : User | c.delete[u]) or
        c.stutter[]
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
