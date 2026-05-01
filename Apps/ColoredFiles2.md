# app: `ColoredFiles2`

* **types**:
    * a set of `File`s
    * a set of `Color`s
* **concepts**:
    * one `Trash[File]` named `T`
    * one `Label[File,Color]` named `L`
* **views**:
    * `colors` = `L.labels`
* **design goal**:
    * Only `accessible` or `trashed` files can be labeled with colors.
* **priority to reactions**: yes
* **reactions**:
```
reaction empty_clear
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f]

reaction affix_error
when
	L.affix[f,c]
when
	f not in T.accessible and f not in T.trashed
then
	error
```
* **formalizations**: [Alloy](ColoredFiles2.als), [TLA+](ColoredFiles2.tla)