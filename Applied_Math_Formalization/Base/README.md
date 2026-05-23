# Applied_Math_Base heap directory

This directory exists solely to host the `Applied_Math_Base` session declared in
`../ROOT`. That session has no theories of its own; it sits on `HOL-Analysis` and
bakes the vendored `Munkres_Topology_Local` theories into a heap image so that
`Topology_Bridge` and the rest of `Applied_Math_Nonemptiness` stay editable
(interactively reprocessed) without rebuilding Munkres each time.

Build the heap once with:

```bash
isabelle build -d . -d ../../Imported_Munkres_Topology Applied_Math_Base
```

then launch jEdit on the editable theories with `-l Applied_Math_Base`.
