# app: `FileSharing1`

* **types**:
    * a set of `File`s
    * a set of `Token`s
* **concepts**:
    * one `Trash[File]` named `T`
    * one `Permalink[File,Token]` named `P`
* **invariants**:
    * a `File` has a `Token` in its `urls` that can still be accessed iff that `Token` was shared when the `File` was `accessible`, and the `Token` has not been `accessed` in the meantime, nor the `File` has been deleted.
* **views**:
    * `uploaded` = the set of `File`s that have been created
    * `shared` = the set of `Token`s that have been shared for each `File` and not yet revoked
* **reactions**:
```
reaction delete_revoke
when
	T.delete[f]
where
	t in f.shared
then
	P.revoke[t]

reaction access_revoke
when
	P.access[t]
then
	P.revoke[t]

reaction share_error
when
	P.share[f,t]
where
	f not in uploaded - T.trashed
then
    error

reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed and shared.t not in T.trashed
then
    error
```
* **formalizations**: [Alloy](FileSharing1.als)