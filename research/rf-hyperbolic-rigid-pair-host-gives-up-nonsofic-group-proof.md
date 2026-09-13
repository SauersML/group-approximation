---
rg: 2
id: rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group-proof
kind: route
title: Delzant's large injectivity radius on a deep normal subgroup, then integer lamps over the restricted pair
target: rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group
requires: [sofic-groups-kill-rigid-compression-defects]
---

Notation as in the claim.  `X` is the Cayley graph of `G` for a finite
generating set.  Edges have length 1, and `X` is a geodesic `delta`-hyperbolic
space.  `|g|` is word length.

**Input (Delzant).**  T. Delzant, *Sur l'anneau d'un groupe hyperbolique*,
C. R. Acad. Sci. Paris 324, Série I (1997) 381-384, read from the author's PDF
on 2026-09-12.

- Define `[g] = inf_(p in H) |gp - p|` and `rho = inf_(g != e) [g]`.
- PROPOSITION, p. 382: "Si G est un groupe d'isométries d'un espace
  δ-hyperbolique H dont le rayon d'injectivité est supérieur à 4δ, alors G
  satisfait la propriété de factorisation unique forte."
- His definition, p. 382, includes the unique product property: for finite
  sets `A, B` not reduced to a point, some element of `AB` has a unique
  expression `ab`.

Kionke--Raimbault (arXiv:1411.6449v2, p. 3) record the virtual form: "any
residually finite, word-hyperbolic group contains with finite index a diffuse
subgroup (the same statement for unique products was proven earlier by T.
Delzant [24])".

**1. A deep normal subgroup has unique products.**

- *Small displacement is conjugate to short.*  Let `g != 1` and `p in X` with
  `|gp - p| <= 4 delta + 1`.  Some vertex `h` lies within `1/2` of `p`.  Then
  `g' = h^-1 g h` moves `p' = h^-1 p`, which lies within `1/2` of `e`, by the
  same amount.  So `|g'| = d(g' e, e) <= 4 delta + 2`.
- *Choose `G_k`.*  The set `F = {g != 1 : |g| <= 4 delta + 2}` is finite.  By
  residual finiteness, some normal subgroup `G_k` of finite index misses `F`.
- *Large radius.*  For `g in G_k \ {1}`, every conjugate of `g` lies in `G_k`,
  hence outside `F`.  So `|gp - p| > 4 delta + 1` for every `p`, and the
  injectivity radius of `G_k` on `X` is at least `4 delta + 1`.
- *Conclusion.*  Delzant's Proposition gives unique products for `G_k`.  A
  nontrivial finite subgroup `A` has no unique product in `AA`, so `G_k` is
  torsion-free.

**2. Restricting the pair.**  `E_k` is normal of finite index in `E`, and
`Gamma_k` has finite index in `Gamma`.  Property (T) passes to finite-index
subgroups, so both are Kazhdan.

*Lemma.*  If a subsemigroup `P` generates a group `E` and `N` is a normal
subgroup of finite index, then `P cap N` generates `N`.

*Proof of the lemma.*

- Let `e` be the exponent of `E/N` and `H' = <P cap N>`.
- For `p in P` we have `p^e in P cap N`.
- For `s in P cap N`, the element `p s p^(e-1)` lies in `P` and maps to
  `p^e = 1` in `E/N`.  So it lies in `H'`, and hence
  `p s p^-1 = (p s p^(e-1)) p^-e` lies in `H'`.
- So every `p in P` normalizes `H'`, and so does `p^-1 = p^(e-1) p^-e`.
  Therefore `H'` is normal in `E`.
- In `E/H'` each image of `p` has order dividing `e`.  So every element of `E`
  is congruent mod `H'` to a positive word `w` in `P`.
- For `n in N`, such a `w` lies in `n H' <= N`, hence in `P cap N <= H'`.  So
  `n` lies in `H'`.  ∎

*Infranormality.*

- Apply the lemma with `P = P_Gamma` computed in `E`, and `N = E_k`.
- If `g in P_Gamma cap E_k`, then `g Gamma g^-1 <= Gamma` and
  `g G_k g^-1 = G_k`.  So `g Gamma_k g^-1 <= Gamma_k`, and `g` lies in the
  compression semigroup of `Gamma_k` in `E_k`.
- By the lemma that semigroup generates `E_k`.

*Non-normality.*

- Some `u in P_Gamma` compresses strictly: otherwise `P_Gamma`, and so `E`,
  would normalize `Gamma`.
- Put `f = [Gamma : u Gamma u^-1] >= 2`, possibly infinite.  Then
  `[Gamma : u^j Gamma u^-j] = f^j`.
- Take `j` a multiple of the exponent of `E/E_k` with `2^j > [Gamma : Gamma_k]`.
  Then `u^j in E_k`, and `u^j Gamma_k u^-j <= u^j Gamma u^-j cap G_k <= Gamma_k`.
- The first group has index at least `2^j > [Gamma : Gamma_k]` in `Gamma`.  So
  `u^j Gamma_k u^-j != Gamma_k`, and `Gamma_k` is not normal in `E_k`.

**3. `W` is not sofic.**  Let `o = Gamma_k` and `z = e_o`.

- `z` centralizes `Gamma_k`.
- Take a strict compressor `t` of `Gamma_k` in `E_k`, and `gamma` in `Gamma_k`
  outside `t Gamma_k t^-1`.  Then
  `[t z t^-1, gamma] = e_(t o) - e_(gamma t o) != 0`.
- This is the computation of
  `left-orderable-non-sofic-via-integer-lamp-rigid-pair`, step 2.
- `W` is countable and carries a nontrivial rigid defect, so it is not sofic by
  `sofic-groups-kill-rigid-compression-defects`.

**4. `W` has unique products.**

- `L = direct_sum Z` is torsion-free abelian, hence left-orderable.  So it has
  unique products: `max_(a in A) a b_max` has a unique expression.
- `W/L = E_k <= G_k` has unique products.

*Extensions.*  Let `N` be normal in `E'`, with `N` and `E'/N` having unique
products, and let `A, B` be finite nonempty subsets of `E'`.

- In `E'/N` pick a product `c_bar` with a unique expression `a_bar b_bar`.
- Put `A_1 = A cap a_bar` and `B_1 = B cap b_bar`.  The products in `AB` lying
  over `c_bar` are exactly `A_1 B_1`.
- Fix `a_0 in A_1` and `b_0 in B_1`.  Then `A' = a_0^-1 A_1` and
  `B' = B_1 b_0^-1` lie in `N`, and `A_1 B_1 = a_0 (A' B') b_0`.
- A uniquely expressed `x = a' b'` in `A' B'` gives
  `a_0 x b_0 = (a_0 a')(b' b_0)`, uniquely expressed in `AB`.

So `W` has unique products.  ∎
