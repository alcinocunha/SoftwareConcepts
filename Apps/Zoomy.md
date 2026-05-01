# app: `Zoomy`

* **types**:
    * a set of `User`s
    * a set of `Content`s
* **concepts**:
    * one `Owning[User,Meeting]` named `OM`
    * one `Owning[Meeting,Chat]` named `OC`
    * a set of `Meeting[User]`
    * a set of `Chat[User,Content]`
* **views**:
    * `scheduled` = `OM.owns`
    * `chat` = `OC.owns`
* **design goal**:
    * The `host` is the user that scheduled the meeting.
    * Each active meeting has exactly one chat, and the non-active meetings have no chat.
    * The participants of a meeting are exactly the same that are joined to the respective chat.
* **priority to reactions**: yes
* **reactions**:
```
reaction start_acquire
when
    m.start[u]
then
    some c : Chat | OC.acquire[m,c]

reaction end_release
when
    m.end[u]
then
    OC.release[m,m.chat]

reaction end_leave
when
    m.end[h]
where
    c in m.chat and u in c.joined.Time
then
    c.leave[u]

reaction join_join
when
    m.join[u]
where
    c in m.chat
then
    c.join[u]

reaction leave_leave
when
    m.leave[u]
where
    c in m.chat
then
    c.leave[u]

reaction start_error
when
    m.start[u]
where
    m not in u.scheduled
then
    error

reaction release_meeting_error
when
    OM.release[u,m]
where
    some m.host
then
    error

reaction join_error
when
    c.join[u]
where
    no (chat.c).host or u not in (chat.c).participants
then
    error

reaction leave_error
when
    c.leave[u]
where
    u in (chat.c).participants
then
    error

reaction acquire_chat_error
when
    OC.acquire[m,c]
where
    no m.host or some m.chat
then
    error

reaction release_chat_error
when
    OC.release[m,c]
where
    some m.host
then
    error
```
* **formalizations**: [Alloy](Zoomy.als), [TLA+](Zoomy.tla)