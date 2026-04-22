# app: `Restaurant1`

* **types**:
    * a set of `Table`s
    * a set of `Client`s
    * one label `Reserved`
* **concepts**:
    * one `Reservation[Client,Table]` named `R`
    * one `Label[Table,Reserved]` named `L`
* **views**:
    * `tables` = `R.available`
    * `reservations` = the subset of `R.reservations` where the reserved table was not used yet
    * `reserved` = the tables with the `Reserved` label
* **design goal**:
    * The tables with the `Reserved` label are exactly the reserved tables that have not been used yet.
* **priority to reactions**: yes
* **reactions**:
```
reaction reserve_affix
when
	R.reserve[c,t]
then
	L.affix[t,Reserved] 

reaction cancel_detach
when
	R.cancel[c,t]
then
	L.detach[t,Reserved] or L.clear[t]

reaction use_detach
when
	R.use[c,t]
then
	L.detach[t,Reserved] or L.clear[t]

reaction affix_error
when
	L.affix[t,Reserved]
where
	t not in Client.reservations
then
	error

reaction detach_error
when
	L.detach[t,Reserved]
where
	t in Client.reservations
then
	error

reaction clear_error
when
	L.clear[t]
where
	t in Client.reservations
then
	error
```
* **formalizations**: [Alloy](Restaurant1.als), [TLA+](Restaurant1.tla)