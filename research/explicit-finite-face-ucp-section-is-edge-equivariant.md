---
rg: 2
id: explicit-finite-face-ucp-section-is-edge-equivariant
kind: claim
title: The finite face of the triangle relator extension has an explicit ucp section that is exact on one edge
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  triangle-relator-extension-admits-local-ucp-sections: that asks for ucp lifts of every finite-dimensional operator system of the whole colimit algebra; this supplies one in closed form for the single finite face `C^*(P_13)` and proves nothing about any operator system meeting the rest of the group.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that is the equivalence identifying LLP of the colimit with local splitting; this constructs one explicit section of that extension over a finite subalgebra and is a fragment of the positive side, not a reformulation of it.
  position-window-ucp-sections-collapse-to-folner-vectors: that proves the same averaging shape cannot be run over the infinite colimit; this exhibits it working on the finite face, and the two are the same computation read at a finite and an infinite index set.
---

**ESTABLISHED.**  Work in the triangle setting of
`triangle-colimit-llp-reduces-to-relator-local-splitting`: `G_0=P_12 *_(P_2)
P_23`, `E=<P_1 u P_3>=P_1 *_(P_0) P_3 <= G_0`, `q:C^*(G_0)->>C^*(Lambda)`, and
the finite group `P:=P_13`, whose image in `Lambda` is `P` itself, so that
`C^*(P) subset C^*(Lambda)` is a finite-dimensional operator system (indeed a
subalgebra).  Let `sigma:P->E` be any set section of the surjection
`q_E:E->>P` (`sigma(1)=1`).  Define

```text
Theta(u_p) := |P|^(-1) sum_(x in P) u_(sigma(x))^* u_(sigma(xp)),
                                     p in P.                 (FF1)
```

Then

```text
(a) Theta extends to a ucp map C^*(P) -> C^*(E) subset C^*(G_0);
(b) q o Theta = incl : C^*(P) -> C^*(Lambda);                (FF2)
(c) if sigma is right P_1-equivariant, i.e. sigma(xh)=sigma(x)h for
    all x in P, h in P_1, then Theta is a right C^*(P_1)-module map:
    Theta(a b)=Theta(a) b for all a in C^*(P), b in C^*(P_1);
    in particular Theta(u_h)=u_h for every h in P_1.
```

Such a `sigma` exists: the right `P_1`-orbits on `P` are the left cosets
`xP_1`, `P_1` acts freely on `P`, so choose one representative per coset and
propagate.

Proof: `explicit-finite-face-ucp-section-proof`.

**Scope, stated honestly.**  Existence of *some* ucp section over `C^*(P)` is
not new and is not the point: `C^*(P)` is finite-dimensional, hence nuclear,
so Choi--Effros already lifts every ucp map out of it.  The content is that the
section is written in closed form from a set section, that its positivity proof
is a single Hilbert-module matrix coefficient rather than an abstract lifting
theorem, and that `(c)` makes it **exact on one edge**: all of the
incompatibility with the ambient algebra is pushed onto the `P_3` side.  This
is the precise form of the "one-edge defect" idea, and it is the natural base
case for any inductive attack on
`triangle-relator-extension-admits-local-ucp-sections`.

**Why it does not globalize, and why that is consistent.**  `(FF1)` is exactly
an orthogonal-position/window section in the sense of
`position-window-ucp-sections-collapse-to-folner-vectors`, with position index
running over `P` and constant coefficients `|P|^(-1/2)`.  That no-go forces the
associated scalar vector to be right-translation invariant; over the finite `P`
the normalized indicator of `P` *is* invariant, which is why `(FF1)` exists,
and over the infinite `Lambda` no nonzero finitely supported vector is, which is
why the same formula cannot be run there.  The two nodes are one computation at
two index sets, and the boundary between them is finiteness of the face.
