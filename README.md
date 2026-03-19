# Software Concepts

Daniel Jackson's [software concepts](https://essenceofsoftware.com) formalized using [Alloy](https://alloytools.org). 

The repository includes both formal models of the individual concepts and apps built by composing those concepts using syncronization rules.

# Index of Concepts

| Concept | Used in |
|---------|---------|
| [Label](Concepts/Label.als) | [FileSystem1](Apps/FileSystem1.als) [FileSystem2](Apps/FileSystem2.als) [FileSystem3](Apps/FileSystem3.als) |
| [Trash](Concepts/Trash.als) | [FileSystem1](Apps/FileSystem1.als) [FileSystem2](Apps/FileSystem2.als) [FileSystem3](Apps/FileSystem3.als) [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) |

# Index of Apps

| App | Uses |
|-----|------|
| [FileSystem1](Apps/FileSystem1.als) | [Trash](Concepts/Trash.als) [Label](Concepts/Label.als) |
| [FileSystem2](Apps/FileSystem2.als) | [Trash](Concepts/Trash.als) [Label](Concepts/Label.als) |
| [FileSystem3](Apps/FileSystem3.als) | [Trash](Concepts/Trash.als) [Label](Concepts/Label.als) |
| [NoSecretsInTrash1](Apps/NoSecretsInTrash1.als) | [Trash](Concepts/Trash.als) |
| [NoSecretsInTrash2](Apps/NoSecretsInTrash2.als) | [Trash](Concepts/Trash.als) |
