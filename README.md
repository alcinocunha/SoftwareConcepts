# Software Concepts

Daniel Jackson's [software concepts](https://essenceofsoftware.com) formalized using [Alloy](https://alloytools.org). 

The repository includes both formal models of the individual concepts and apps built by composing those concepts using synchronization rules. For some apps, we include versions with and without Priority to Reactions (PR), with the former being usually simpler.

# Index of Concepts

| Concept | Parameters |      State      | Actions | Used in |
|---------|-------|-------------|-----|------|
| [Chat](Concepts/Chat.als) | `User` `Content` | `joined ⊆ User × Time` `messages ⊆ Message` `read ⊆ User × Message` | `join` `leave` `send` `delete` `read`| [Zoomy](Apps/WOPR/Zoomy.als) |
| [Label](Concepts/Label.als) | `Item` `Tag` | `labels ⊆ Item × Tag` | `affix` `detach` `clear` | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [Restaurant1](Apps/Restaurant1.als) |
| [Meeting](Concepts/Meeting.als) | `User` | `host ⊆ User` `participants ⊆ User` | `start` `join` `leave` `end` | [Zoomy](Apps/WOPR/Zoomy.als) |
| [Messaging](Concepts/Messaging.als) | `User` `Content` | `inbox ⊆ User × Message` `read ⊆ User × Message` `sent ⊆ Message` | `send` `read` `delete` | [Restaurant2](Apps/WOPR/Restaurant2.als) |
| [Owning](Concepts/Owning.als) | `User` `Thing` | `owns ⊆ User × Thing` | `acquire` `release` | [OnlineDrive](Apps/OnlineDrive.als) [Zoomy](Apps/WOPR/Zoomy.als) |
| [Permalink](Concepts/Permalink.als) | `Resource` `URL` | `urls ⊆ Resource × URL` `revoked ⊆ URL` | `share` `revoke` `access` | [FileSharing1](Apps/WOPR/FileSharing1.als) [FileSharing2](Apps/WOPR/FileSharing2.als) [FileSharing3](Apps/WOPR/FileSharing3.als) |
| [Reservation](Concepts/Reservation.als) | `User` `Resource` | `available ⊆ Resource` `reservations ⊆ User × Resource` | `provide` `retract` `reserve` `cancel` `use` | [Restaurant1](Apps/WOPR/Restaurant1.als) [Restaurant2](Apps/WOPR/Restaurant2.als) |
| [Trash](Concepts/Trash.als) | `Item` | `accessible ⊆ Item` `trashed ⊆ Item` | `create` `delete` `restore` `empty` | [ColoredFiles1](Apps/WOPR/ColoredFiles1.als) [ColoredFiles2](Apps/WOPR/ColoredFiles2.als) [ColoredFiles3](Apps/WOPR/ColoredFiles3.als) [FileSharing1](Apps/WOPR/FileSharing1.als) [FileSharing2](Apps/WOPR/FileSharing2.als) [FileSharing3](Apps/WOPR/FileSharing3.als) [NoSecretsInTrash1](Apps/WOPR/NoSecretsInTrash1.als) [NoSecretsInTrash2](Apps/WOPR/NoSecretsInTrash2.als) [OnlineDrive](Apps/WOPR/OnlineDrive.als) |
| [WebApp](Concepts/WebApp.als) | `User` | `registered ⊆ User` `loggedin ⊆ User` | `register` `login` `logout` `delete` |  [OnlineDrive](Apps/WOPR/OnlineDrive.als) |

# Index of Apps

| App w/o PR | App w/ PR | Uses | Description |
|-----|-----|----|-----|
| [ColoredFiles1](Apps/WOPR/ColoredFiles1.als) | [ColoredFiles1](Apps/WPR/ColoredFiles1.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Accessible files can be labeled with a color. When the file is deleted the colors are removed. |
| [ColoredFiles2](Apps/WOPR/ColoredFiles2.als) | [ColoredFiles2](Apps/WPR/ColoredFiles2.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Both accessible and trashed files can be labeled with a color. When the trash is emptied the colors are removed. |
| [ColoredFiles3](Apps/WOPR/ColoredFiles3.als) | [ColoredFiles3](Apps/WPR/ColoredFiles3.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Both accessible and trashed files can be labeled with a color.  The special color red is used to label trashed files, and added or removed automatically when the file is deleted or restored. When the trash is emptied the colors are removed. |
| [FileSharing1](Apps/WOPR/FileSharing1.als) | [FileSharing1](Apps/WPR/FileSharing1.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | Files can be shared via single use permalinks. When a file is deleted or a permalink is accessed, the permalink is revoked. User cannot directly revoke permalinks. |
| [FileSharing2](Apps/WOPR/FileSharing2.als) | [FileSharing2](Apps/WPR/FileSharing2.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | Files can be shared via single use permalinks. Permalinks are kept when the file is deleted, but cannot be accessed unless the file is restored. When the trash is emptied all permalinks are revoked. User cannot directly revoke permalinks. |
| [FileSharing3](Apps/WOPR/FileSharing3.als) | [FileSharing3](Apps/WPR/FileSharing3.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | When a file is created it is automatically shared via a permalink. When the permalink is accessed, the file is deleted, the permalink is revoked, and the trash is emptied. User cannot directly delete and share files or revoke permalinks. |
| [NoSecretsInTrash1](Apps/WOPR/NoSecretsInTrash1.als) | [NoSecretsInTrash1](Apps/WPR/NoSecretsInTrash1.als) | [Trash](Concepts/Trash.als) | Secret files cannot be in the trash. When a secret file is deleted the trash is emptied, possibly leading to the loss of other files. |
| [NoSecretsInTrash2](Apps/WOPR/NoSecretsInTrash2.als) | [NoSecretsInTrash2](Apps/WPR/NoSecretsInTrash2.als) | [Trash](Concepts/Trash.als) | Secret files cannot be in the trash. When a secret file is deleted the non-secret files are temporarily restored before the trash is emptied. |
| [OnlineDrive](Apps/OnlineDrive.als) |  | [Owning](Concepts/Owning.als) [Trash](Concepts/Trash.als) [WebApp](Concepts/WebApp.als) | A simple online drive with trash functionality. |
| [Restaurant1](Apps/WOPR/Restaurant1.als) | [Restaurant1](Apps/WPR/Restaurant1.als) | [Label](Concepts/Label.als) [Reservation](Concepts/Reservation.als) | A restaurant where reserved tables are automatically assigned a Reserved label. |
| [Restaurant2](Apps/WOPR/Restaurant2.als) | [Restaurant2](Apps/WPR/Restaurant2.als) | [Messaging](Concepts/Messaging.als) [Reservation](Concepts/Reservation.als) | A restaurant that confirms reservations via messages and keeps track of active reservations by the messages in its outbox. |
| [Zoomy](Apps/Zoomy.als) |  | [Chat](Concepts/Chat.als) [Meeting](Concepts/Meeting.als) [Owning](Concepts/Owning.als) | A simple video conferencing app where when a chat is created when a meeting starts. The owning concept is used in two different ways, for hosts to schedule meetings, and for meetings to acquire chats. Currently it has a potential deadlock issue, since there is no order enforced between the reactions that make users leave the chat and that delete the chat messages when a meeting ends. |

