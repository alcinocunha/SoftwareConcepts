# concept: `Permalink[Resource,URL]`

## Specification

```
concept: Permalink[Resource,URL]
purpose: To allow sharing resources via URLs.
principle: If a resource is shared via a URL, then it can be accessed via that URL, but if the URL is revoked then it cannot be accessed.
state:
    urls: Resource -> set URL
    accessed: set URL
    revoked: set URL
actions:
    share(r:Resource, u:URL)
        requires: u is not in the urls of any resource
        effects: adds u to the urls of r
    revoke(u:URL)
        requires: u is in the urls of some resource and is not revoked
        effects: adds u to revoked
    access(u:URL)
        requires: u is in the urls of some resource and is not revoked
        effects: adds u to accessed
invariants: revoked and accessed only contain URLs that are in the urls of some resource
```

## Formalizations

* [Alloy](Permalink.als)
* [TLA+](Permalink.tla)