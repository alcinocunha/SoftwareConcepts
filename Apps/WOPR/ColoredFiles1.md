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
* **priority to reactions**: no
* **reactions**:
```
reaction delete_with_colors
when
	T.delete[f]
where
	some f.colors
then
	L.clear[f] or (one f.colors and L.detach[f,c]) or T.restore[f] or T.empty[]

reaction affix_not_accessible
when
	L.affix[f,c]
where
	f not in T.accessible
then
	L.detach[f,c] or T.restore[f] or L.clear[f] or T.create[f]

reaction empty_with_colors
when
	T.empty[]
where
	f in trashed and some f.colors
then
	L.clear[f] or (one f.colors and L.detach[f,f.colors]) or T.create[f]
```
* **formalizations**: [Alloy](ColoredFiles1.als)