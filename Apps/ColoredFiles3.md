# app: `ColoredFiles3`

* **types**:
    * a set of `File`s
    * a set of `Color`s
    * a special `Color` named `Red`
* **concepts**:
    * one `Trash[File]` named `T`
    * one `Label[File,Color]` named `L`
* **views**:
    * `colors` = `L.labels`
* **design goal**:
    * Only `accessible` or `trashed` files can be labeled with colors.
    * A file is in `trashed` iff it has the `Red` color.
* **priority to reactions**: yes
* **reactions**:
```
reaction empty_clear
when
	T.empty[]
where
	f in T.trashed
then
	L.clear[f]

reaction delete_affix
when
	T.delete[f]
then
	L.affix[f,Red]

reaction restore_detach
when
	T.restore[f]
then
	L.detach[f,Red]

reaction affix_error
when
	L.affix[f,c]
where
	f not in T.accessible and f not in T.trashed
then
	error

reaction affix_red_error
when
	L.affix[f,Red]
where
	f in T.accessible
then
	error

reaction detach_red_error
when
	L.detach[f,Red]
where
	f in T.trashed
then
	error

reaction clear_red_error
when
	L.clear[f]
where
	f in T.trashed and Red in f.colors
then
	error
```
* **formalizations**: [Alloy](ColoredFiles3.als), [TLA+](ColoredFiles3.tla)