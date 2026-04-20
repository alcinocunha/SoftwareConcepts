----------------- MODULE Label -----------------

CONSTANT Label, Item, Tag

VARIABLE labels, occurred

Init ==
    /\ labels = [ c \in Label |-> [i \in Item |-> {}] ]
    /\ occurred = <<>>

affix(c, i, l) ==
    /\ l \notin labels[c][i]
    /\ labels' = [labels EXCEPT ![c][i] = @ \cup {l}]
    /\ occurred' = <<c, "affix", i, l>>

detach(c, i, l) ==
    /\ l \in labels[c][i]
    /\ labels' = [labels EXCEPT ![c][i] = @ \ {l}]
    /\ occurred' = <<c, "detach", i, l>>

clear(c, i) ==
    /\ labels[c][i] # {}
    /\ labels' = [labels EXCEPT ![c][i] = {}]
    /\ occurred' = <<c, "clear", i>>

Next == \E c \in Label:
    \/ \E i \in Item, l \in Tag: affix(c, i, l)
    \/ \E i \in Item, l \in Tag: detach(c, i, l)
    \/ \E i \in Item: clear(c, i)

Spec == Init /\ [][Next]_<<labels, occurred>>

Invariant == \A l \in Label:
    labels[l] \in [Item -> SUBSET Tag]

===============================================

