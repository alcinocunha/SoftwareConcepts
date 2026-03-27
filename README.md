# Software Concepts

Daniel Jackson's [software concepts](https://essenceofsoftware.com) formalized using [Alloy](https://alloytools.org). 

The repository includes both formal models of the individual concepts and apps built by composing those concepts using syncronization rules.

# Index of Concepts

| Concept | Parameters | State | Actions | Used in |
|---------|-------|-------------|-----|------|
| [Label](Concepts/Label.als) | `Item` `Tag` | `labels : Item -> Tag` | `affix` `detach` `clear` | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [Restaurant](Apps/Restaurant.als) |
| [Permalink](Concepts/Permalink.als) | `Resource` `URL` | `urls : Resource -> URL` `revoked : set URL` | `share` `revoke` `access` | [FileSharing1](Apps/FileSharing1.als) |
| [Reservation](Concepts/Reservation.als) | `Resource` | `available : set Resource` `reservations : User -> Resource` | `provide` `retract` `reserve` `cancel` `use` | [Restaurant](Apps/Restaurant.als) |
| [Trash](Concepts/Trash.als) | `Item` | `accessible : set Item` `trashed : set Item` | `create` `delete` `restore` `empty` | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [FileSharing1](Apps/FileSharing1.als) [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) [OnlineDrive](Apps/OnlineDrive.als) |

# Index of Apps

| App | Uses | Description |
|-----|------|-----|
| [ColoredFiles1](Apps/ColoredFiles1.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Accessible files can be labeled with a color. When the file is deleted the colors are removed. |
| [ColoredFiles2](Apps/ColoredFiles2.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Both accessible and trashed files can be labeled with a color. When the trash is emptied the colors are removed. |
| [ColoredFiles3](Apps/ColoredFiles3.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) | Both accessible and trashed files can be labeled with a color.  The special color red is used to label trashed files, and added or removed automatically when the file is deleted or restored. When the trash is emptied the colors are removed. |
| [FileSharing1](Apps/FileSharing1.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) | Files can be shared via single use permalinks. When a file is deleted or a permalink is accessed, the permalink is revoked. |
| [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) | [Trash](Concepts/Trash.als) | Secret files cannot be in the trash. When a secret file is deleted the trash is emptied, possibly leading to the loss of other files. |
| [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) | [Trash](Concepts/Trash.als) | Secret files cannot be in the trash. When a secret file is deleted the non-secret files are temporarily restored before the trash is emptied. |
| [OnlineDrive](Apps/OnlineDrive.als) | [Trash](Concepts/Trash.als) | A simple online file drive with trash functionality, where each user has their own trash. |
| [Restaurant](Apps/Restaurant.als) | [Label](Concepts/Label.als) [Reservation](Concepts/Reservation.als) | A restaurant reservation system where reserved tables are automatically assigned a Reserved label. |
