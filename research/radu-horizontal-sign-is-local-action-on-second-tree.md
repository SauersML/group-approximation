---
rg: 2
id: radu-horizontal-sign-is-local-action-on-second-tree
kind: claim
title: The sign carrying Radu's mark is the local action of the horizontal lattice on a star of the second Bruhat-Tits tree, so its kernel fixes a framed vertex at the second prime
distinct_from:
  radu-horizontal-quotient-is-arithmetic-lattice: that finds the S_3-vertex p of the second tree and proves transitivity; this computes how the horizontal letters a, b, c act on the star of p
  radu-delta-squared-orbit-is-signed-permutation-module: that defines the sign character psi' combinatorially from the square relators; this identifies its restriction to <a,b,c> with a congruence condition at the second prime
  radu-square-lamp-forces-reflections-in-finite-actions: that is the finite-set consequence of the mark; this is the arithmetic reason finite quotients cannot separate the sign
  radu-xz-slab-is-second-tree-edge-stabilizer: that identifies the slab <a,b,c,x,z> with an edge stabilizer of the second tree and psi' with the local sign sgn_6 on the edge's neighbourhood; this uses the same local computation for <a,b,c> to identify the kernel C_chi with the fixator of a star, and the edge coset space Q/C_chi with a double cover of framed vertices
artifacts:
  - research/artifacts/radu-edge-lamp-host-and-square-firewall-2026-09-13.md
  - research/artifacts/radu-h4-star-check.py
  - research/artifacts/radu-h4-star-check-part2.py
  - research/artifacts/radu-h4-star-check-output-2026-09-13.txt
---

Review 2026-09-13 (`ex-verify2-groups`, `research/artifacts/ex-review2-groups-2026-09-13-part9.md` §4): the derivations from the computed local actions PASS, but the local actions come from fixed-precision 2-adic arithmetic (truncation modulo 2^71, divisions, valuation thresholds, no precision tracking). That is strong evidence, not proof: GAP until the valuations are certified, for example in Sage `Qp` with tracked precision or by exact integral arithmetic modulo 2^k.

**ESTABLISHED (unreviewed; 2-adic check).** Notation of
`radu-horizontal-quotient-is-arithmetic-lattice` and `radu-metabelian-quotient-embeds-in-edge-lamp-wreath`:
`Q ⊂ PGL_2(F_𝔮) × PGL_2(F_𝔮')` acts on `T_h × T'`, and `p ∈ T'` is the vertex fixed by
`S_3 = <xz, xyx>`. Let `C = <a,b,c>`, `χ(a) = χ(b) = 1`, `χ(c) = −1`, and `C_χ = ker χ = <a,b,cac,cbc>`.

1. **The horizontal lattice fixes `p`.** `ρ(a)`, `ρ(b)`, `ρ(c)` fix `p`. On the three edges at `p`,
   `a` and `b` act trivially, and `c` fixes the edge `[p, xp]` and swaps `[p, xy·p]` and `[p, zy·p]`.
   `radu-xz-slab-is-second-tree-edge-stabilizer` (item 2) computed the same local action
   independently, with a different script; the two computations agree.
2. **The sign is local.** `χ` is the permutation character of `C` on the star of `p`:

   ```text
   C_χ = C ∩ K,        K := Fix_Q(star of p) = C_χ ⊔ xz·c·C_χ.
   ```

   `K` acts simply transitively on the vertices of `T_h`.
3. **Framed vertices.** `Q/K` is the `Q`-set of framed vertices of `T'`, i.e. vertices with a
   labelling of their three edges. The edge coset space `Q/C_χ` of
   `radu-edge-coset-action-is-sofic` is a double cover of it, embedded diagonally in
   `V(Y) × Q/K`. So if that coset action is sofic, the action of `Q` on the framed vertices of its
   second tree is sofic.

**Reading.** Radu's mark `(xz)^4` is twice the signed square lamp in `G_2`. The sign is a congruence
condition at `𝔮'` on the horizontal lattice `C`. `𝔮'` is inverted in the `S`-arithmetic group `Q`,
so the profinite topology of `Q` does not see it. That is why every finite quotient forces a
reflection (`radu-square-lamp-forces-reflections-in-finite-actions`), and why any sofic model has
to "see the second prime" approximately.

Proof in `radu-horizontal-sign-is-local-action-on-second-tree-proof`.
