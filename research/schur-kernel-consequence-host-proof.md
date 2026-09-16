---
rg: 2
id: schur-kernel-consequence-host-proof
kind: route
title: Factor the coefficient map through the quotient adjunction or the solving host, then read Mayer--Vietoris rationally
target: schur-kernel-shrinks-along-consequences-and-hosts
requires:
  - aspherical-adjunction-has-zero-schur-kernel
  - amenable-t-shape-adjunctions-kill-no-schur-class
artifacts:
  - research/artifacts/sp4-schur-deligne-packet-pruning-2026-09-16.md
---

Full proofs: artifact, Section 1 (Lemmas 1.1, 1.3, 1.4 and Corollary 1.2).

**(CM1).** `deg_t : Q * <t> -> Z` is a homomorphism. Writing
`w = prod_i g_i u^{e_i} g_i^{-1}` with `e_i = ±1` gives
`deg_t w = (sum_i e_i) deg_t u`. Since `<<w>> <= <<u>>`, there is a quotient
map `r : A_w -> A_u` with `q_u = r o q_w`. Hence `q_{u*} = r_* o q_{w*}`, and
`ker q_{w*} <= ker q_{u*}`. If `beta` is any multiplier with
`ev(beta)(K_2(Q, w)) != 0`, the larger group `K_2(Q, u)` is also detected.

**(CM2).** Let `v in <<u>>` be nonsingular. By (CM1), `u` is nonsingular and
`K_2(Q, v) <= K_2(Q, u)`. Under the first hypothesis,
`aspherical-adjunction-has-zero-schur-kernel` gives `K_2(Q, u) = 0`. Under
the second, `amenable-t-shape-adjunctions-kill-no-schur-class` gives
`K_2(Q, u) = 0`. Proper powers `u^k` and products of conjugates of
`u^{±1}` lie in `<<u>>`.

**(CM3).** The homomorphism `Q * <t> -> L` given by `phi` on `Q` and
`t -> l` kills `w`. So it factors as `s o (Q * <t> -> A_w)` with
`s o q = phi`. Then `phi_* = s_* o q_*` and `ker q_* <= ker phi_*`. For the
last clause take `L = Q` and `phi = id`.

**(CM4).** The Mayer--Vietoris sequence of the amalgam,
`H_2(C; Q) -> H_2(Q; Q) + H_2(D; Q) -> H_2(P; Q)`, has zero first term, so
the middle map is injective, and so is its restriction to `H_2(Q; Q)`. The
HNN sequence `H_2(C; Q) -> H_2(Q; Q) -> H_2(P; Q)` also has zero first
term. Composites of injections are injective. Rational homology commutes
with directed colimits, and a class that dies in the colimit dies at a
finite stage. For a root adjunction, `C = <c>` is cyclic, so
`H_2(C; Q) = 0`. Finally, if `y in ker phi_*` and `phi_* (x) Q` is
injective, then `y (x) 1 = 0`, so `y` is torsion.
