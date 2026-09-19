---
rg: 2
id: fix-boone-higman-linear-char-zero-route-no-suslin
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.RouteNoSuslin: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/RouteNoSuslin.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-bhmet-char-zero-host-host`, `fix-bhmet-elem-fpk2-poly-deg-spans`, `fix-bhmet-elem-fpk2-surj-stab-vec`, `fix-bhmet-envelope-higman-vc-tau-d2-class-a`, `fix-bhmet-envelope-higman-vc-tau-d2-class-ab`, `fix-bhmet-envelope-higman-vc-tau-d2-class-ob`, `fix-bhmet-envelope-higman-vc-tau-hop-f2-hop`, `fix-bhmet-pure-char-prime-e-high-artin-hasse-alg`, `fix-bhmet-suslin-r2-ind-dilate`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.RouteNoSuslin` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
