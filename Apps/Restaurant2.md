# app: `Restaurant2`

* **types**:
    * a set of `User`s
    * a subset of `User`s called `Client`
    * a user named `Restaurant` that is not in `Client`
    * a set of `Table`s
* **concepts**:
    * one `Reservation[Client,Table]` named `R`
    * one `Messaging[User,Table]` named `M`
* **views**:
    * `tables` = `R.available`
    * `reservations` = the subset of `R.reservations` where the reserved table was not used yet
* **design goal**:
    * The active `reservations` are exactly those that are confirmed by messages in the restaurant's outbox.
    * There is at most one confirmation message per table in the restaurant's outbox.
* **priority to reactions**: yes
* **reactions**:
```
reaction send_confirmation
when
    R.reserve[c,t]
then
    M.send[Restaurant,c,t]

reaction use_delete
when
    R.use[c,t]
where
    m in M.outbox[Restaurant] and m.to = c and m.content = t
then
    M.deleteFromOutbox[Restaurant,m]

reaction cancel_delete
when
    R.cancel[c,t]
where
    m in M.outbox[Restaurant] and m.to = c and m.content = t
then
    M.deleteFromOutbox[Restaurant,m]

reaction send_error
when
	M.send[Restaurant,u,t]
where
	t not in u.reservations or t in Restaurant.outbox.content
then
    error

reaction delete_error
when
    M.deleteFromOutbox[Restaurant,m]
where
    m.content in m.to.reservations
then
    error    
```
* **formalizations**: [Alloy](Restaurant2.als), [TLA+](Restaurant2.tla)