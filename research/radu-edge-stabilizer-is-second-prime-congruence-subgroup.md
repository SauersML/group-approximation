---
rg: 2
id: radu-edge-stabilizer-is-second-prime-congruence-subgroup
kind: claim
title: The horizontal lattice of Radu's quotient and its sign kernel are congruence subgroups at the second prime, fixators of an edge neighbourhood of the second tree
distinct_from:
  radu-horizontal-sign-is-local-action-on-second-tree: that proves C_chi = C cap Fix_Q(star of p) and that Q/C_chi double covers framed vertices; this proves C_chi = Q cap Fix(N(e')) with no intersection with C, so Q/C_chi is itself a single orbit in L/K for a compact open K of the second factor
  radu-xz-slab-is-second-tree-edge-stabilizer: that identifies the slab <a,b,c,x,z> with the setwise stabilizer of e'; this identifies <a,b,c> and its sign kernel with 2-adically open subgroups of the pointwise stabilizer of e'
---

Review 2026-09-13 (`ex-verify2-groups`, `research/artifacts/ex-review2-groups-2026-09-13-part9.md` §4): the derivations from the computed local actions PASS, but the local actions come from fixed-precision 2-adic arithmetic (truncation modulo 2^71, divisions, valuation thresholds, no precision tracking). That is strong evidence, not proof: GAP until the valuations are certified, for example in Sage `Qp` with tracked precision or by exact integral arithmetic modulo 2^k.

**ESTABLISHED (unreviewed; rests on the 2-adic local computations of the two nodes above).** Let
`Q ⊂ L := PB^×(F_(𝔮')) ≅ PGL_2(Q_2)` act on the second tree `T'`, where the embedding is `ρ` at `𝔮'`,
which is injective. Let `e' = {p, q}` with `q = x·p`, and let `N(e') = {p, q, p_1, p_2, q_1, q_2}` be
the six vertices at distance at most 1 from `e'`. Put `C = <a,b,c>`, `C_χ = <a, b, cac, cbc>` and
`E = Fix_Q(p) ∩ Fix_Q(q)`. For `g ∈ E` let `sign_p(g)` and `sign_q(g)` be the signs of `g` on
`{p_1, p_2}` and on `{q_1, q_2}`. Then

```text
C    = E ∩ ker(sign_q)            = Q ∩ K_C,     K_C := {g ∈ Fix_L(e') : g fixes q_1 and q_2},
C_χ  = E ∩ ker(sign_q) ∩ ker(sign_p) = Q ∩ K_χ,   K_χ := Fix_L(N(e')).
```

`K_C` and `K_χ` are compact open in `L`. Consequently

```text
Q/C_χ  ≅  Q·K_χ  ⊆  L/K_χ,          Q/C  ≅  Q·K_C  ⊆  L/K_C
```

as `Q`-sets. The edge coset action of `radu-edge-coset-action-is-sofic` is the action of `Q` on one
orbit of framed edge neighbourhoods of its second tree. It is an instance of the coset action
`A ↷ A/(A ∩ K)` in `homogeneous-quotient-soficity-gives-vertex-soficity`, with `L = PGL_2(Q_2)`,
`K = K_χ` and `A = Q`.

**Proof.**
* *Indices.* `C` acts simply transitively on `V(T_h)`, and `Fix_Q(p)` acts on `V(T_h)` with vertex
  stabilizer `W ∩ Fix_Q(p) = S_3` (`radu-horizontal-quotient-is-arithmetic-lattice`, item 1), so
  `[Fix_Q(p) : C] = 6`. The action of `Fix_Q(p)` on the three edges at `p` is `S_3`, so
  `[Fix_Q(p) : E] = 3`. `C ⊆ E`, since `a, b, c` fix `p` and `q`
  (`radu-xz-slab-is-second-tree-edge-stabilizer`, item 1). Hence `[E : C] = 2`.
* *Local signs.* By `research/artifacts/radu-second-tree-slab-output-2026-09-13.txt`, `a` and `b` fix
  `N(e')` pointwise, `c = (p_1 p_2)`, and `xz = (p_1 p_2)(q_1 q_2)`, with `xz ∈ E`. So `sign_q` is a
  character of `E` that is trivial on `C` and takes the value `−1` at `xz`.
* *First identity.* `ker(sign_q) ⊇ C`, and both have index 2 in `E`, so `C = E ∩ ker(sign_q)`.
* *Second identity.* On `C`, `sign_p(a) = sign_p(b) = 1` and `sign_p(c) = −1`, so `sign_p|_C = χ`
  and `C_χ = C ∩ ker(sign_p)`. An element of `E` with both signs `+1` fixes each outer pair pointwise,
  so `E ∩ ker(sign_q) ∩ ker(sign_p) = Fix_Q(N(e'))`.
* *Openness.* `E = Q ∩ Fix_L(e')`, and the signs are restrictions of the continuous permutation
  characters of `Fix_L(e')` on the two outer pairs. So `C = Q ∩ K_C` and `C_χ = Q ∩ K_χ`, and `K_C`,
  `K_χ` are the stated compact open subgroups.
* *Orbits.* `aC_χ ↦ aK_χ` is well defined and injective, since `Q ∩ K_χ = C_χ`.
* *Consistency.* `xz·c = (q_1 q_2)` fixes the star of `p` and lies outside `C_χ`, which recovers
  `Fix_Q(star p) = C_χ ⊔ xzc·C_χ` of `radu-horizontal-sign-is-local-action-on-second-tree`. ∎
