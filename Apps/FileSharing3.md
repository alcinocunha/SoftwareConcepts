# app: `FileSharing3`

* **types**:
    * a set of `File`s
    * a set of `Token`s
* **concepts**:
    * one `Trash[File]` named `T`
    * one `Permalink[File,Token]` named `P`
* **design goal**:
    * there are no `trashed` files
    * Each `accessible` `File` has exactly one non `revoked` `Token`
    * The set of `revoked` `Token`s is the same as the set of `accessed` `Token`s
* **priority to reactions**: yes
* **views**:
    * `uploaded` = the set of `File`s that have been created
    * `shared` = the set of `Token`s that have been shared for each `File` and not yet revoked
* **reactions**:
```
reaction create_share
when
	T.create[f]
then
	some t : Token | P.share[f,t]

reaction access_revoke
when
	P.access[t]
then
	P.revoke[t]

reaction access_delete
when
	P.access[t]
where
	t in f.shared
then
	T.delete[f]

reaction access_empty
when
	P.access[t]
then
	T.empty[]

reaction share_error
when
	P.share[f,t]
where
	f not in uploaded or some f.shared
then
	error

reaction delete_error
when
	T.delete[f]
where
	some f.shared and f.shared not in P.accessed
then
	error

reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed  
then
	error
```
* **formalizations**: [Alloy](FileSharing3.als), [TLA+](FileSharing3.tla)