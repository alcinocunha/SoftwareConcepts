# Software Concepts

Daniel Jackson's [software concepts](https://essenceofsoftware.com) formalized using [Alloy](https://alloytools.org). 

The repository includes both formal models of the individual concepts and apps built by composing those concepts using syncronization rules.

# Index of Concepts

| Concept | Used in |
|---------|---------|
| [Label](Concepts/Label.als) | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [Restaurant](Apps/Restaurant.als) |
| [Permalink](Concepts/Permalink.als) | [FileSharing1](Apps/FileSharing1.als) |
| [Reservation](Concepts/Reservation.als) | [Restaurant](Apps/Restaurant.als) |
| [Trash](Concepts/Trash.als) | [ColoredFiles1](Apps/ColoredFiles1.als) [ColoredFiles2](Apps/ColoredFiles2.als) [ColoredFiles3](Apps/ColoredFiles3.als) [FileSharing1](Apps/FileSharing1.als) [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) [OnlineDrive](Apps/OnlineDrive.als) |

# Index of Apps

| App | Uses |
|-----|------|
| [ColoredFiles1](Apps/ColoredFiles1.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) |
| [ColoredFiles2](Apps/ColoredFiles2.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) |
| [ColoredFiles3](Apps/ColoredFiles3.als) | [Label](Concepts/Label.als) [Trash](Concepts/Trash.als) |
| [FileSharing1](Apps/FileSharing1.als) | [Permalink](Concepts/Permalink.als) [Trash](Concepts/Trash.als) |
| [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) | [Trash](Concepts/Trash.als) |
| [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) | [Trash](Concepts/Trash.als) |
| [OnlineDrive](Apps/OnlineDrive.als) | [Trash](Concepts/Trash.als) |
| [Restaurant](Apps/Restaurant.als) | [Label](Concepts/Label.als) [Reservation](Concepts/Reservation.als) |
