---
rg: 2
id: radu-horizontal-quotient-is-arithmetic-lattice
kind: claim
title: The horizontal quotient of Radu's BMW lattice has finite index in the S-arithmetic normalizer of a maximal order over Q(sqrt17), so it is a cocompact arithmetic lattice in PGL_2(Q_2)^2
distinct_from:
  radu-horizontal-quotient-is-quaternionic-s-arithmetic: that proves the quotient is a discrete subgroup of the S-arithmetic group; this asks that it have finite index there, i.e. be a lattice
---

**OPEN.** `Q = Γ_R/Λ_v`, embedded in `N(O)/F^×` by
`radu-horizontal-quotient-is-quaternionic-s-arithmetic`, has finite index there. Then `Q` is a
cocompact irreducible arithmetic lattice in `PGL_2(Q_2) × PGL_2(Q_2)`, and Radu's
non-residually-finite lattice is an extension of an infinitely generated free group by an
arithmetic lattice acting on the same kind of product of two 3-regular trees.

Equivalently: `ρ(V)` acts cocompactly on the tree `T'` at the second prime `𝔮'` above 2.

## Attempts

* **Euler characteristic numerology (consistent, not a proof).**
  * The horizontal splitting descends to `Q = ρ(V) *_(ρ(V_a)) ρ(E_a)`, so
    `χ(Q) = −χ(ρ(V))/2`.
  * If `ρ` is faithful on the Coxeter group `W = <x,y,z | x^2,y^2,z^2,(xz)^2,(xyz)^3> ≅ PGL_2(Z)`,
    then `χ(W) = −1/12` and `χ(Q) = 1/24`.
  * `ζ_(Q(√17))(−1) = ζ(−1) L(−1, χ_17) = (−1/12)(−B_(2,χ_17)/2) = 1/3`, with
    `B_(2,χ_17) = (1/17) Σ χ_17(a) a^2 = 136/17 = 8`.
  * The Euler characteristic formula for `S`-arithmetic unit groups of totally definite
    quaternion algebras, as recalled here but not re-read from Serre, gives
    `χ(O^1_S) = 2^(−n) ζ_F(−1) ∏_(𝔭∈S)(1 − N𝔭) = 1/12` for `n = 2` and `S = {𝔮, 𝔮'}`. This
    normalization reproduces `χ = −1/12` for the Hurwitz units with `1/3` inverted.
  * So `χ(O^1_S/±1) = 1/6`, and `Q = N(O)/F^×` would need `[N(O)/F^× : O^1_S/±1] = 4`. That
    index is plausible, since the totally positive `S`-units modulo squares have order 4. It is
    unverified.
* **What a proof needs.** Either
  * faithfulness of `ρ` on `W` and an exact index computation; or
  * a vertex `p ∈ T'` fixed by `<ρ(xz), ρ(xyx)> ≅ S_3`, permuted transitively on its three
    edges, with an inversion in `ρ(V)` on one of them. Then `ρ(V)` is transitive on the vertices
    of `T'`. This is a computation over a ramified extension of `Q_2`.
