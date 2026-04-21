# app: `FileSharing1`

* **types**:
    * a set of `File`s
    * a set of `Token`s
* **concepts**:
    * one `Trash[File]` named `T`
    * one `Permalink[File,Token]` named `P`
* **design goal**:
    * a `File` has a `Token` in its `urls` that can still be accessed iff that `Token` was shared when the `File` was `accessible`, and the `Token` has not been `accessed` in the meantime, nor the `File` has been permanently deleted.
    * a token is in `accessed` iff it was accessed while the corresponding file was accessible.
* **priority to reactions**: yes
* **views**:
    * `uploaded` = the set of `File`s that have been created
    * `shared` = the set of `Token`s that have been shared for each `File` and not yet revoked
* **reactions**:
```
reaction empty_revoke
when
	T.empty[]
where
	f in T.trashed and t in f.shared
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
	f not in uploaded
then
	error

reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed and shared.t in uploaded
then
	error

reaction access_error
when
	P.access[t]
where
	shared.t in T.trashed
then
	error
```
* **formalizations**: [Alloy](FileSharing2.als)