--------- MODULE Zoomy ---------

EXTENDS TLC, Naturals

VARIABLES action, reactions

error == FALSE

CONSTANTS Meeting, Chat, User, Content, MaxTime, None

ASSUME None \notin User /\ None \notin Nat

Symmetry == Permutations(User) \cup Permutations(Content) \cup Permutations(Meeting) \cup Permutations(Chat)

VARIABLES time, sent, joined, reads, host, participants, owns_meeting, owns_chat

vars == <<action, reactions, time, sent, joined, reads, host, participants, owns_meeting, owns_chat>>

M == INSTANCE Meeting
C == INSTANCE Chat
OM == INSTANCE Owning WITH Owning <- {"OM"}, Resource <- Meeting, owns <- owns_meeting
OC == INSTANCE Owning WITH Owning <- {"OC"}, User <- Meeting, Resource <- Chat, owns <- owns_chat

scheduled == owns_meeting["OM"]
chat == owns_chat["OC"]

Actions == M!Actions \cup C!Actions \cup OM!Actions \cup OC!Actions

InitAction == action \in Actions
NextAction == action' \in Actions

InitConcepts ==
    /\ M!Init
    /\ C!Init
    /\ OM!Init
    /\ OC!Init

NextConcepts ==
    /\ M!Next
    /\ C!Next
    /\ OM!Next
    /\ OC!Next

Invariant ==
    \* A user can only host a meeting if they have scheduled it
    /\ (\A u \in User, m \in Meeting: u = host[m] => m \in scheduled[u])
    \* Started meetings must have a chat, and the chat must be unique to that meeting
    /\ \A m \in Meeting: host[m] # None <=> chat[m] # {}
    /\ \A m \in Meeting, c1, c2 \in Chat: c1 \in chat[m] /\ c2 \in chat[m] => c1 = c2
    \* The users joined in the chat must be exactly the participants of the meeting
    /\ \A c \in Chat: (\E u \in User: joined[c][u] # None) => (\E m \in Meeting: c \in chat[m])
    /\ \A m \in Meeting, c \in Chat: c \in chat[m] => participants[m] = { u \in User: joined[c][u] # None }

\* Reactions

(*
reaction start_acquire
when
    m.start[u]
then
    some c : Chat | OC.acquire[m,c]
*)

start_acquire_add == { <<r, m>> \in {"start_acquire"} \X Meeting : \E u \in User : M!start(m,u) }
start_acquire_remove == { <<r, m>> \in {"start_acquire"} \X Meeting : \E c \in Chat : OC!acquire("OC",m,c) }

(*
reaction end_release
when
    m.end[u]
then
    OC.release[m,m.chat]
*)

end_release_add == { <<r, m>> \in {"end_release"} \X Meeting : \E u \in User : M!end(m,u) }
end_release_remove == { <<r, m>> \in {"end_release"} \X Meeting : \E c \in Chat : c \in chat[m] /\ OC!release("OC",m,c) }

(*
reaction end_leave
when
    m.end[h]
where
    c in m.chat and u in c.joined.Time
then
    c.leave[u]
*)

end_leave_add == { <<r, c, u>> \in {"end_leave"} \X Chat \X User : \E h \in User, m \in Meeting: M!end(m,h) /\ c \in chat[m] /\ joined[c][u] # None }
end_leave_remove == { <<r, c, u>> \in {"end_leave"} \X Chat \X User : C!leave(c,u) }

(*
reaction join_join
when
    m.join[u]
where
    c in m.chat
then
    c.join[u]
*)

join_join_add == { <<r, c, u>> \in {"join_join"} \X Chat \X User : \E m \in Meeting: M!join(m,u) /\ c \in chat[m] }
join_join_remove == { <<r, c, u>> \in {"join_join"} \X Chat \X User : C!join(c,u) }

(*
reaction leave_leave
when
    m.leave[u]
where
    c in m.chat
then
    c.leave[u]
*)

leave_leave_add == { <<r, c, u>> \in {"leave_leave"} \X Chat \X User : \E m \in Meeting: M!leave(m,u) /\ c \in chat[m] }
leave_leave_remove == { <<r, c, u>> \in {"leave_leave"} \X Chat \X User : C!leave(c,u) }

(*
reaction start_error
when
    m.start[u]
where
    m not in u.scheduled
then
    error
*)

start_error_add == { <<r>> \in {<<"start_error">>} : \E m \in Meeting, u \in User : M!start(m,u) /\ m \notin scheduled[u] }
start_error_remove == { <<r>> \in {<<"start_error">>} : error }

(*
reaction release_meeting_error
when
    OM.release[u,m]
where
    some m.host
then
    error
*)

release_meeting_error_add == { <<r>> \in {<<"release_meeting_error">>} : \E m \in Meeting, u \in User : OM!release("OM",u,m) /\ host[m] # None }
release_meeting_error_remove == { <<r>> \in {<<"release_meeting_error">>} : error }

(*
reaction join_error
when
    c.join[u]
where
    no (chat.c).host or u not in (chat.c).participants
then
    error
*)

join_error_add == { <<r>> \in {<<"join_error">>} : \E c \in Chat, u \in User : C!join(c,u) /\ ((\A m \in Meeting: c \notin chat[m]) \/ (\E m \in Meeting: c \in chat[m] /\ (host[m] = None \/ u \notin participants[m]))) }
join_error_remove == { <<r>> \in {<<"join_error">>} : error }

(*
reaction leave_error
when
    c.leave[u]
where
    u in (chat.c).participants
then
    error
*)

leave_error_add == { <<r>> \in {<<"leave_error">>} : \E c \in Chat, u \in User : C!leave(c,u) /\ (\E m \in Meeting: c \in chat[m] /\ u \in participants[m]) }
leave_error_remove == { <<r>> \in {<<"leave_error">>} : error }

(*
reaction acquire_chat_error
when
    OC.acquire[m,c]
where
    no m.host or some m.chat
then
    error
*)

acquire_chat_error_add == { <<r>> \in {<<"acquire_chat_error">>} : \E m \in Meeting, c \in Chat : OC!acquire("OC",m,c) /\ (host[m] = None \/ chat[m] # {}) }
acquire_chat_error_remove == { <<r>> \in {<<"acquire_chat_error">>} : error }

(*
reaction release_chat_error
when
    OC.release[m,c]
where
    some m.host
then
    error
*)

release_chat_error_add == { <<r>> \in {<<"release_chat_error">>} : \E m \in Meeting, c \in Chat : OC!release("OC",m,c) /\ host[m] # None }
release_chat_error_remove == { <<r>> \in {<<"release_chat_error">>} : error }

\* Reaction semantics

reactions_to_add == start_acquire_add \cup end_release_add \cup end_leave_add \cup join_join_add \cup leave_leave_add \cup start_error_add \cup release_meeting_error_add \cup join_error_add \cup leave_error_add \cup acquire_chat_error_add \cup release_chat_error_add
reactions_to_remove == start_acquire_remove \cup end_release_remove \cup end_leave_remove \cup join_join_remove \cup leave_leave_remove \cup start_error_remove \cup release_meeting_error_remove \cup join_error_remove \cup leave_error_remove \cup acquire_chat_error_remove \cup release_chat_error_remove 

InitReactions ==
    /\ reactions = {}

NextReactions ==
    /\ reactions # {} => reactions_to_remove \cap reactions # {}
    /\ reactions' = (reactions \ reactions_to_remove) \cup reactions_to_add

Spec == InitAction /\ InitConcepts /\ InitReactions /\ [][NextAction /\ NextConcepts /\ NextReactions]_vars

Design == reactions = {} <=> Invariant

================================