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
    * O
* **priority to reactions**: yes
* **reactions**:
```
```
* **formalizations**: [Alloy](FileSystem.als)