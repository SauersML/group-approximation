---
rg: 2
id: loop-braid-desc-links-simply-connected-via-colimit
kind: route
title: "L_n(LB_*) is simply connected for n ≥ 8: strict fundamental domain OM(K_n) plus the colimit of stabilizers, via a covering argument"
target: loop-braid-descending-links-are-eventually-simply-connected
requires:
  - ordered-matching-complex-kn-simply-connected-n-ge-8
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
artifacts:
  - research/artifacts/zp-loop-braid-descending-links-simply-connected-2026-09-16.md
---

Take `N = 8`. For `n ≥ 8` let `P = PLB_n` act on `X = L_n(LB_*)`. The proof is artifact §§2–3 and §7.

1. **Fundamental domain.** By the colimit claim's setup (artifact Lemmas 2.2–2.4):
   - the simplices `[s, Γ]` with s a permutation braid form a strict fundamental domain `Q ≅ OM(K_n)`;
   - stabilizers fix simplices pointwise.
2. **Q is simply connected.** Q is non-empty, connected and simply connected by
   `ordered-matching-complex-kn-simply-connected-n-ge-8`.
3. **Colimit.** The quotient of `∗_v P_v` by the edge identifications maps isomorphically onto P, by
   `pure-loop-braid-group-is-colimit-of-cabling-stabilizers` (`n ≥ 7`).
4. **Covering criterion (artifact Proposition 3.1, proved there in full).** Let a group act on a
   simplicial complex with a strict fundamental domain Q, with stabilizers fixing simplices pointwise
   and Q connected and simply connected. If the vertex-edge colimit of the stabilizers maps
   isomorphically onto the group, the complex is simply connected.
   - Take the universal cover `p: X̃ → X` and a lift `j: Q → X̃`.
   - Each stabilizer `P_σ` lifts uniquely to automorphisms fixing `j(b_σ)`, and these fix `j(σ)`
     pointwise and agree on overlaps. So they define a homomorphism from the colimit into the group of
     lifts, i.e. a section `s: P → G̃`.
   - `Z = ⋃_g s(g) j(Q)` maps injectively to X, because Q is a strict fundamental domain and `s(P_σ)`
     fixes `j(σ)`.
   - Z is closed under passing to adjacent simplices, so `Z = X̃`. Hence p is a homeomorphism.
5. **Conclusion.** Steps 1–4 give that `L_n(LB_*)` is simply connected for every `n ≥ 8`.
