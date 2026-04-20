module Reaction
open Action

abstract sig Reaction {}

var sig reactions, reactions_to_add, reactions_to_remove in Reaction {}

fact {
	no reactions
	always {
		reactions' = (reactions - reactions_to_remove) + reactions_to_add
	}
}

pred PriorityToReactions {
    always {
        some reactions and some action implies some reactions & reactions_to_remove
    }
}

pred error {
    some none
}