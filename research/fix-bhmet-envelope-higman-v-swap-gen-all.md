---
rg: 2
id: fix-bhmet-envelope-higman-v-swap-gen-all
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll: failed to synthesize instance of type class"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVSwapGenAll.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVSwapGenAll.lean:157:8: failed to synthesize instance of type class
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVSwapGenAll.lean:158:9: failed to synthesize instance of type class
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVSwapGenAll.lean:157:13: unsolved goals
error: GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVSwapGenAll.lean:168:14: Unknown constant `GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_closure_eq_top`
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-envelope-higman-v-swap-gen-all`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
