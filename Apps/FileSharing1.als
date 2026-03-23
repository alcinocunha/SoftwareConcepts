module Apps/FileSharing1
open Action[User]
open Reaction

// Composed concepts

open Concepts/Trash[User,File]
open Concepts/Token[User,File,Token]

// Single user app

one sig User {}

// Types

sig File {}
sig Token {}

// The app invariant

// Files with active (not revoked or accessed) tokens must be accessible
check Invariant {
always {
no Reaction iff tokens.(Token-revoked-accessed) in User.accessible
}
} for 2 but 7 Action, 1 Reaction expect 0

// Scenarios

// A shared file is deleted
// Then a reaction will either restore the file or disable its active token
run Scenario {
	some f : File, t : Token {
		create[User,f];share[User,f,t];delete[User,f]
	}
	eventually always no Reaction
} for exactly 1 File, exactly 1 Token, 7 Action, 1 Reaction expect 1

// Reactions

/*
when
f not in User.accessible and some f.tokens-revoked-accessed
then
restore[User,f] or revoke[User,f,t] or access[User,t]
*/

var lone sig InaccessibleFileWithActiveToken extends Reaction { }

fact {
always {
some InaccessibleFileWithActiveToken iff {
some f : File | before {
not (
restore[User,f]
or some t : f.tokens-revoked-accessed | revoke[User,f,t] or access[User,t]
) since (f not in User.accessible and some f.tokens-revoked-accessed)
}
}
}
}

// Preventions

/*
when
share[User,f,t]
require
f in User.accessible
*/

fact {
all f : File, t : Token | always {
share[User,f,t] implies f in User.accessible
}
}

/*
when
access[User,t]
require
some tokens.t & User.accessible
*/

fact {
all t : Token | always {
access[User,t] implies some tokens.t & User.accessible
}
}
