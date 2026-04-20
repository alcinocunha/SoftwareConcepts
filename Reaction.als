module Reaction
open Action

abstract sig Reaction {}

var sig reactions in Reaction {}

pred false {
    some none
}