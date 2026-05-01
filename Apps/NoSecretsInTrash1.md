# app: `NoSecretsInTrash1`

* **types**:
    * a set of `File`s
    * a set of `Secret` `File`s
* **concepts**:
    * one `Trash[File]` named `T`
* **invariants**:
    * There are no `Secret` files in `trashed`
* **reactions**:
```
reaction delete_empty
when
	T.delete[f]
where
	f in Secret
then
	T.empty[]
```
* **formalizations**: [Alloy](NoSecretsInTrash1.als), [TLA+](NoSecretsInTrash1.tla)