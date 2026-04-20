# concept: `Label[Iten,Tag]`
 
* **purpose**: To allow labeling items with tags.
* **principle**: If a tag is affixed to an item, then it remains affixed until it is detached or all tags of the item are cleared.
* **state**:
    * a set of `Item`s with
        * a `labels` set of `Tag`s
* **actions**:
    * `affix(i:Item, t:Tag)`
        * **requires**: `t` is not a label of `i`
        * **effects**: adds `t` to the labels of `i`
    * `detach(i:Item, t:Tag)`
        * **requires**: `t` is a label of `i`
        * **effects**: removes `t` from the labels of `i`
    * `clear(i:Item)`
        * **requires**: `i` has at least one label
        * **effects**: removes all labels from `i`
* **formalizations**: [Alloy](Label.als), [TLA+](Label.tla)