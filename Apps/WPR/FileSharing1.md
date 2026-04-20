# app: `FileSharing1`

* **types**:
    * a set of `File`s
    * a set of `Token`s
* **concepts**:
    * one `Trash[File]`
    * one `Permalink[File,Token]`
* **design goal**:
    * the `urls` of a `File` that can still be accessed are those that were shared when the `File` was `accessible`, and which have not been `accessed` yet, nor the `File` has been deleted.
* **reactions**:
```
reaction delete_revoke
when
	delete[f]
where
	t in f.shared
then
	P.revoke[t]

reaction download_revoke
when
	download[t]
then
	P.revoke[t]

reaction share_error
when
	share[f,t]
where
	f not in uploaded - trashed
then

reaction revoke_error
when
	P.revoke[t]
where
	t not in P.accessed and shared.t not in trashed
then
```
* **formalizations**: [Alloy](FileSharing1.als)