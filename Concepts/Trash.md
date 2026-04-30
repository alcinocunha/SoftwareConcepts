# Trash

## Specification

```
concept: Trash[Item]
purpose: To allow undoing the deletion of items.
principle: If an item is deleted, it can be restored, and if restored becomes accessible again.
state:
    accessible: set Item
    trashed: set Item
actions:
    create(f:Item)
        requires: f is not in accessible or trashed
        effects: adds f to accessible
    delete(f:Item)
        requires: f is in accessible
        effects: moves f from accessible to trashed
    restore(f:Item)
        requires: f is in trashed
        effects: moves f from trashed to accessible
    empty()
        requires: trashed is not empty
        effects: removes all items in trashed
invariants: accessible and trashed are disjoint
```

## Formalizations

* [Alloy](Trash.als)
* [TLA+](Trash.tla)