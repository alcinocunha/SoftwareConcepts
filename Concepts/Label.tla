----------------- MODULE Label -----------------

CONSTANT Label, Item, Tag

VARIABLE labels, action

Actions == Label \X {"affix", "detach"} \X Item \X Tag \cup Label \X {"clear"} \X Item

InitAction == action \in Actions
NextAction == action' \in Actions

Init ==
    /\ labels = [ c \in Label |-> [i \in Item |-> {}] ]

affix(c, i, l) ==
    /\ action = <<c, "affix", i, l>>
    /\ l \notin labels[c][i]
    /\ labels' = [labels EXCEPT ![c][i] = @ \cup {l}]


detach(c, i, l) ==
    /\ action = <<c, "detach", i, l>>
    /\ l \in labels[c][i]
    /\ labels' = [labels EXCEPT ![c][i] = @ \ {l}]

clear(c, i) ==
    /\ action = <<c, "clear", i>>
    /\ labels[c][i] # {}
    /\ labels' = [labels EXCEPT ![c][i] = {}]

stutter(c) ==
    /\ action[1] # c
    /\ labels' = labels

Next == \E c \in Label:
    \/ \E i \in Item, l \in Tag: affix(c, i, l)
    \/ \E i \in Item, l \in Tag: detach(c, i, l)
    \/ \E i \in Item: clear(c, i)
    \/ stutter(c)

Spec == InitAction /\ Init /\ [][NextAction /\ Next]_<<labels, action>>

Invariant == \A l \in Label:
    labels[l] \in [Item -> SUBSET Tag]

===============================================

