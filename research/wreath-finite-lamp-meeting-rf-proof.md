---
rg: 2
id: wreath-finite-lamp-meeting-rf-proof
kind: route
title: Restrict lamps to the finite invariant support of the lamp part
target: wreath-subgroups-meeting-lamps-finitely-are-rf
requires: []
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Derivation (artifact Proposition 7.1).

- **Invariant support.** The union `S` of the supports of `N' = G' ∩ ⊕_X A` is finite.
  It is invariant under the image `Q'` of `G'`, because `N'` is normal in `G'` and
  pointwise conjugation preserves supports.
- **An injective homomorphism.** `(n, g) -> (n|_S, g)` is a homomorphism into
  `A^S ⋊ Q'`, since `g^-1 S = S`. Its kernel lies in `N'` and has trivial restriction to
  `S`, so it is trivial.
- **The target is residually finite.** `Q'` acts on `S` through a finite quotient with
  kernel `K`. So `A^S × K` is a finite-index subgroup that is residually finite.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 17 of the
verification artifact). The conjugate `w nu w^-1 = (n (g.nu) n^-1, 1)` has
support `g supp(nu)`, so `g S = S`.
