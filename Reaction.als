module Reaction
open Action

abstract var sig Reaction {}

pred false {
    some none
}

pred PriorityToReactions {
    always {
        some Reaction and some Action implies {
            some r : Reaction | r not in Reaction'
        }
    }
}