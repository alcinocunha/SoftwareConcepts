# concept: `Permalink[Resource,URL]`

* **purpose**: To allow sharing resources via URLs.
* **principle**: If a resource is shared via a URL, then it can be accessed via that URL, but if the URL is revoked then it cannot be accessed.
* **state**
    * a set of `Resource`s with
        * a `urls` set of `URL`s
    * a `revoked` set of `URL`s
    * an `accessed` set of `URL`s
* **actions**:
    * `share(r:Resource, u:URL)`
        * **requires**: `u` is not a URL of any resource
        * **effects**: adds `u` to the URLs of `r`
    * `revoke(u:URL)`
        * **requires**: `u` is a URL of some resource and is not revoked
        * **effects**: adds `u` to `revoked`
    * `access(u:URL)`
        * **requires**: `u` is a URL of some resource and is not revoked
        * **effects**: adds `u` to `accessed`
* **invariants**:
    * `revoked` and `accessed` only contain URLs of shared resources
* **formalizations**: Alloy [Permalink.als](Permalink.als)