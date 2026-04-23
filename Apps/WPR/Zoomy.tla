--------- MODULE Zoomy ---------

VARIABLES action, reactions

error == FALSE

CONSTANTS Meeting, Chat, User, Content, MaxTime

VARIABLES time, messages, joined, reads, host, participants, scheduled, chat

vars == <<action, reactions, time, messages, joined, reads, host, participants, scheduled, chat>>

OM == "OM"
OC == "OC"

================================