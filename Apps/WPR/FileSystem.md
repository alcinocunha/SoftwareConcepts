# app: `FileSystem`

* **types**:
    * a set of `Object`s partitioned into `File`s and `Dir`s
* **concepts**:
    * one `Trash[Object]` named `Root`
    * a disjoint set of `Trash[Object]` named `Other`
    * one `Owning[Dir,Other]` named `O`
* **views**:
    * `content` = `O.owns`
* **invariants**:
    * The non root trashes can only have objects if they are owned by some directory
    * A directory owns a trash iff it is in some trash
    * A directory can only be in one trash and can only contain one trash
    * No cycles
* **priority to reactions**: yes
* **reactions**:
```
reaction create_dir
when 
    t.create(d)
where
    d in Dir
then
    some t : Other | O.acquire(d,t)

reaction empty_dir
when
    t.empty()
where
    d in t.trashed and x in d.content
then
    O.release(d,x)

reaction release_trash_delete_objects
when
    O.release(d,t)
where
    o in t.accessible
then
    t.delete(o)

reaction release_trash_empty
when
    O.release(d,t)
where
    no t.accessible and some t.trashed
then
    t.empty()

reaction delete_last_empty
when
    t.delete(o)
where
    t not in Root and no content.t and t.accessible in o
then
    t.empty()

reaction acquire_error
when
    O.acquire(o,t)
where
    o in File or no (accessible+trashed).o or some o.content or some t.(accessible+trashed)
then
    error

reaction create_error
when
    t.create(o)
where
    t not in Root and no content.t
then
    error

reaction release_error
when
    O.release(d,t)
where
    some (accessible+trashed).d
then
    error
```
* **formalizations**: [Alloy](FileSystem.als), [TLA+](FileSystem.tla)