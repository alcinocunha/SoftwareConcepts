# Software Concepts

Daniel Jackson's [software concepts](https://essenceofsoftware.com) formalized using [Alloy](https://alloytools.org). 

The repository includes both formal models of the individual concepts and apps built by composing those concepts using syncronization rules.

# Index of Concepts

| Concept | Parameters |      State      | Actions | Used in |
|---------|-------|-------------|-----|------|
| [Label](Concepts/Label.als) | `Item` `Tag` | `labels ⊆ Item × Tag` | `affix` `detach` `clear` | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [Restaurant](Apps/Restaurant.als) |
| [Owning](Concepts/Owning.als) | `User` `Thing` | `owns ⊆ User × Thing` | `acquire` `release` | [OnlineDrive](Apps/OnlineDrive.als) |
| [Permalink](Concepts/Permalink.als) | `Resource` `URL` | `urls ⊆ Resource × URL` `revoked ⊆ URL` | `share` `revoke` `access` | [FileSharing1](Apps/FileSharing1.als) [FileSharing2](Apps/FileSharing2.als) [FileSharing3](Apps/FileSharing3.als) |
| [Reservation](Concepts/Reservation.als) | `User` `Resource` | `available ⊆ Resource` `reservations ⊆ User × Resource` | `provide` `retract` `reserve` `cancel` `use` | [Restaurant](Apps/Restaurant.als) |
| [Trash](Concepts/Trash.als) | `Item` | `accessible ⊆ Item` `trashed ⊆ Item` | `create` `delete` `restore` `empty` | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [FileSharing1](Apps/FileSharing1.als) [FileSharing2](Apps/FileSharing2.als) [FileSharing3](Apps/FileSharing3.als) [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) [OnlineDrive](Apps/OnlineDrive.als) |
| [WebApp](Concepts/WebApp.als) | `User` | `registered ⊆ User` `loggedin ⊆ User` | `register` `login` `logout` `delete` |  [OnlineDrive](Apps/OnlineDrive.als) |

# Index of Apps

| App | Uses | Description |
|-----|------|-----|
| [ColoredFiles1](Apps/ColoredFiles1.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Accessible files can be labeled with a color. When the file is deleted the colors are removed. |
| [ColoredFiles2](Apps/ColoredFiles2.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Both accessible and trashed files can be labeled with a color. When the trash is emptied the colors are removed. |
| [ColoredFiles3](Apps/ColoredFiles3.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Both accessible and trashed files can be labeled with a color.  The special color red is used to label trashed files, and added or removed automatically when the file is deleted or restored. When the trash is emptied the colors are removed. |
| [FileSharing1](Apps/FileSharing1.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | Files can be shared via single use permalinks. When a file is deleted or a permalink is accessed, the permalink is revoked. User cannot directly revoke permalinks. |
| [FileSharing2](Apps/FileSharing2.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | Files can be shared via single use permalinks. Permalinks are kept when the file is deleted, but cannot be accessed unless the file is restored. When the trash is emptied all permalinks are revoked. User cannot directly revoke permalinks. |
| [FileSharing3](Apps/FileSharing3.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | When a file is created it is automatically shared via a permalink. When the permalink is accessed, the file is deleted, the permalink is revoked, and the trash is emptied. User cannot directly delete and share files or revoke permalinks. |
| [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) | [Trash](Concepts/Trash.als) | Secret files cannot be in the trash. When a secret file is deleted the trash is emptied, possibly leading to the loss of other files. |
| [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) | [Trash](Concepts/Trash.als) | Secret files cannot be in the trash. When a secret file is deleted the non-secret files are temporarily restored before the trash is emptied. |
| [OnlineDrive](Apps/OnlineDrive.als) | [Owning](Concepts/Owning.als) [Trash](Concepts/Trash.als) [WebApp](Concepts/WebApp.als) | A simple online drive with trash functionality. |
| [Restaurant](Apps/Restaurant.als) | [Label](Concepts/Label.als) [Reservation](Concepts/Reservation.als) | A restaurant reservation system where reserved tables are automatically assigned a Reserved label. |
