# app: `NoSecretsInTrash2`

* **types**:
    * a set of `File`s
    * a set of `Secret` `File`s
* **concepts**:
    * one `Trash[File]` named `T`
* **invariants**:
    * The `trashed` files are the non `Secret` files that have been deleted and not yet restored or emptied when there are no `Secret` files in the trash.
    * The `accessible` files are the files that have been created or restored when there are no `Secret` files in the trash and not yet deleted. 
* **reactions**:
```
reaction delete_empty
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]

reaction delete_restore
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.restore[g]

reaction delete_delete
when
	T.delete[f]
where
	f in Secret and g in trashed - Secret
then
	T.delete[g]

reaction empty_error
when
	T.empty[]
where
	some Secret & trashed and some trashed - Secret
then
	error
```
* **formalizations**: [Alloy](NoSecretsInTrash2.als)