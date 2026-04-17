# concept: Trash [File]

* **purpose**: To allow undoing the deletion of files.
* **principle**: If a file is deleted, it can be restored, and if restored becomes accessible again.
* **state**
    * an `accessible` set of `File`s
    * a `trashed` set of `File`s
* **actions**:
    * `create(f:File)`
        * **requires**: `f` is not in `accessible` or `trashed`
        * **effects**: adds `f` to `accessible`
    * `delete(f:File)`
        * **requires**: `f` is in `accessible`
        * **effects**: moves `f` from `accessible` to `trashed`
    * `restore(f)`
        * **requires**: `f` is in `trashed`
        * **effects**: moves `f` from `trashed` to `accessible`
    * `empty()`
        * **requires**: `trashed` is not empty
        * **effects**: removes all files in `trashed`
* **invariants**:
    * `accessible` and `trashed` are disjoint