# app: `ColoredFiles1`

* **types**:
    * a set of `File`s
    * a set of `Color`s
* **concepts**:
    * one `Trash[File]` named `T`
    * one `Label[File,Color]` named `L`
* **views**:
    * `colors` = `L.labels`
* **design goal**:
    * Only `accessible` files can be labeled with colors.
* **priority to reactions**: yes
* **reactions**:
```
reaction delete_clear
when
	T.delete[f]
where
	some f.colors
then
	L.clear[f]

reaction affix_error
when
	L.affix[f,c]
where
	f not in T.accessible
then
	error
```
* **formalizations**: [Alloy](ColoredFiles1.als), [TLA+](ColoredFiles1.tla)