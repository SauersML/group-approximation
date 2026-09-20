---
rg: 2
id: local-mf-stability-splits-into-rounding-gap-and-path-connection
kind: claim
title: Local MF-stability of a finitely generated group relative to a finitely presented cover is exactly a rounding gap near the exact representations plus a path connection to them; for a Kazhdan kernel the gap alone makes the set of irreducible constituents a homotopy invariant, and without finite quotients every finite approximation is eventually D-quasirandom for every D
distinct_from:
  locally-mf-stable-kazhdan-kernels-collapse-torus-radicals: that uses (LS) as a black box to make torus radicals collapse; this splits (LS) itself into two conditions that fail separately, and measures what each costs a Kazhdan kernel without finite quotients.
  torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel: that is the open existence hole; this does not decide it, but reduces its (LS) to (Gap) and (Conn) and gives a checkable test that refutes (Gap).
  finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts: its Steps A2-A3 prove equal supports for a representation and its twist by a wrap of defect below the Kazhdan constant; Lemma R here is the same Schur argument for two unrelated exact representations of a cover, made uniform over all covers and turned into a homotopy invariant.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that kills local HS stability by deleting one dimension, which costs O(1/sqrt n) in normalized HS but O(1) in operator norm; nothing here transfers that trick, and the operator-norm question stays open.
  mapping-torus-mf-radical-lies-in-finite-residual: that forces (Q) on every witness kernel; Theorem E here turns (Q) plus (T) into quantitative quasirandomness of every finite approximation.
artifacts:
  - research/local-mf-stability-splits-into-gap-and-paths-proof.md
  - research/locally-mf-stable-kazhdan-kernels-collapse-torus-radicals.md
  - research/torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel.md
  - research/finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts.md
---

**ESTABLISHED.** Proof: `local-mf-stability-splits-into-gap-and-paths-proof`.
It imports Shalom's openness of (T) and Mal'cev's theorem. Remark W also imports Dadarlat's Lemma 3.18
(arXiv:2007.12655v2). Nothing else is imported.

## Setting

- `K = F/N` with `F` free on a finite symmetric set `S`. Here `N` is the set of all relators of `K`.
- For a finite set `R ⊆ N`, put `P_R = <S | R>`. `Hom_n(P_R) ⊆ U(n)^S` and
  `dist_R(b) = min_(c ∈ Hom_n(P_R)) max_s ‖b(s) − c(s)‖` are as in
  `locally-mf-stable-kazhdan-kernels-collapse-torus-radicals`. All norms are operator norms.
- An **asymptotic K-representation** is a sequence `b_i ∈ U(n_i)^S` with `‖r(b_i) − 1‖ -> 0` for every
  `r ∈ N`.
- A **uniform K-path family** is a sequence of continuous maps `γ_i : [0,1] -> U(n_i)^S` such that
  `sup_t ‖r(γ_i(t)) − 1‖ -> 0` for every `r ∈ N`.
- For an exact representation `c` of `P_R`, `Supp c` is its finite set of irreducible constituents, up
  to equivalence.
- When `K` is Kazhdan, fix `R_0 ⊆ N` and `κ > 0` as in `finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts`:
  `P_(R_0)` is Kazhdan with constant `κ` for `S`.

**The three conditions, for a fixed finite `R ⊆ N`.**

```text
(LS_R)     every asymptotic K-representation has dist_R(b_i) -> 0.
(Gap_R,θ)  every asymptotic K-representation with dist_R(b_i) ≤ θ for all i has dist_R(b_i) -> 0.
(Conn_R)   every asymptotic K-representation b_i is the endpoint γ_i(1) of a uniform K-path family
           with γ_i(0) ∈ Hom_(n_i)(P_R).
```

(LS) of `torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel` is `(LS_R)` for every `R`.

## Statement

**Theorem S (splitting; no (T) needed).** Let `K` be finitely generated, `R ⊆ N` finite and `θ > 0`. Then

```text
(LS_R)  ⟺  (Gap_R,θ) and (Conn_R).
```

In particular `(Gap_R,θ)` holds for one `θ > 0` exactly when it holds for all of them, given `(Conn_R)`.

**Lemma R (constituent rigidity, uniform over covers).** Let `K` be Kazhdan and `R_0 ⊆ R ⊆ N`. Let `c, c'`
be exact representations of `P_R` of the same dimension with `max_s ‖c(s) − c'(s)‖ < κ`. Then
`Supp c = Supp c'`. The constant `κ` is the same for every `R ⊇ R_0`.

**Theorem H (the gap makes supports homotopy invariant).** Let `K` be Kazhdan, `R_0 ⊆ R ⊆ N`, and assume
`(Gap_R,θ)` for some `θ > 0`. Let `γ_i` be a uniform K-path family with both endpoints `γ_i(0)` and
`γ_i(1)` in `Hom_(n_i)(P_R)`. Then `Supp γ_i(0) = Supp γ_i(1)` for all large `i`.

**Test (T-Gap).** Hence `(Gap_R,θ)`, and with it `(LS)`, fails as soon as some uniform K-path family joins
exact representations of `P_R` with different supports, for infinitely many `i`.

**Theorem E (dimension escape).** Let `K` be Kazhdan with no nontrivial finite quotient, and let
`R_0 ⊆ R_1 ⊆ R_2 ⊆ ...` be finite sets with union `N`. Then:
1. For each `d`, `P_(R_j)` has at most `N(d, κ, |S|)` irreducible `d`-dimensional representations up to
   equivalence. The bound does not depend on `j`.
2. For each `D` there is `j(D)` such that for `j ≥ j(D)` every nontrivial irreducible representation of
   `P_(R_j)` has dimension `> D`.

**Corollary E1 (finite approximations are quasirandom).** Let `K` be as in Theorem E. Let `F_n` be finite
groups and `θ_n : S -> F_n` maps whose images generate `F_n`, such that for each `j` the relators in `R_j`
hold in `F_n` for all large `n`. This covers every LEF approximation. Then for every `D`, for all large
`n`:
- every nontrivial irreducible representation of `F_n` has dimension `> D`;
- `F_n` has no proper subgroup of index `≤ D + 1`;
- in particular `F_n` is perfect.

**Corollary E2 (what (LS) rounds to).** Let `K` be as in Theorem E, let `R_0 ⊆ R` and assume `(LS)`. Let
`b_i` be an asymptotic K-representation and `c_i ∈ Hom_(n_i)(P_R)` with
`max_s ‖b_i(s) − c_i(s)‖ -> 0`. Then:
- for every `D`, for large `i`, every nontrivial member of `Supp c_i` has dimension `> D`;
- every fixed irreducible `σ` of `P_R` lies outside `Supp c_i` for large `i`, unless `σ` is trivial.
So after passing to a subsequence, the sets `Supp c_i ∖ {1}` are pairwise disjoint.

**Remark W (no asymptotically multiplicative ucp lift).** Let `K` be Kazhdan without nontrivial finite
quotients. Let `ψ_n : C*(K) -> M_(k_n)` be unital completely positive maps with
`‖ψ_n(xy) − ψ_n(x) ψ_n(y)‖ -> 0` for all `x, y ∈ C*(K)`. Then `ψ_n(u_s) -> 1` for every `s ∈ S`. So any
asymptotic K-representation that such maps approximate on `S` is asymptotically trivial. This is the
Ozawa--Thom argument (Dadarlat, Proposition 3.19), redone with (Q) in place of residual finiteness.

## What this does to the hole

`torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel` asks for (LS). By Theorem S, (LS)
is now two conditions: a local one, (Gap), and a global one, (Conn).
- **Calibration (not used in any proof, and not verified here).** For `K = Z^2` and `R = {[a,b]}`,
  Voiculescu's almost commuting unitaries have nonzero Bott invariant. That invariant is constant along
  uniform paths and vanishes on commuting pairs, so (Conn) fails. (Gap) is expected to hold there, by
  Lin's theorem that almost commuting unitary pairs with vanishing Bott invariant are near commuting
  pairs. If so, (Conn) can fail while (Gap) holds. No example of the converse is known here.
- **(Gap) is local, and (T) does not give it.** The one-sided Kazhdan projection argument works in any
  C*-algebra. The rounding problem is two-sided, `X ↦ b(g) X c(g)*`, and the only available Kazhdan
  argument for it runs in Hilbert--Schmidt norm on `Hom(H_σ, C^n)`. It loses a factor `sqrt(dim σ)` on
  each constituent `σ`. By Corollary E2 that dimension tends to infinity whenever (Q) holds. So (Q) is
  exactly what makes (Gap) hard for a Kazhdan kernel. Lemma R controls the support of a rounding and
  not its multiplicities.
- **The MF half now has a refutation test.** For a Kazhdan, quotientless MF kernel such as
  `EL_3(LC(X,F_q) ⋊ Z)`, (LS) fails once one uniform K-path family joins two LEF-derived exact
  representations of `P_R` with different supports (Test T-Gap). Corollary E2 says the supports along
  any rounding escape every finite set. Corollary E1 says every finite approximation is eventually
  `D`-quasirandom for every `D`.
- **Weak quasidiagonality is not a way in (Remark W, proved in Step 6 of the route).** The argument of
  Ozawa--Thom (Dadarlat, arXiv:2007.12655v2, Proposition 3.19) shows that no nontrivial MF model of a
  Kazhdan `K` without finite quotients lifts to asymptotically multiplicative unital completely
  positive maps on `C*(K)`. Under (LS) the model
  lifts to *-homomorphisms on `C*(P_R)` instead. The obstruction then sits entirely in the extension
  `0 -> ker(C*(P_R) -> C*(K)) -> C*(P_R) -> C*(K) -> 0`, which is not locally split along the model.
  This is consistent, so it is not a contradiction.

## Scope

- Nothing here decides whether some infinite Kazhdan group without finite quotients satisfies (LS).
  The hole stays OPEN.
- Theorem S uses no (T). Lemma R, Theorem H and Theorem E use (T) only through the uniform constant `κ`.
  Theorem E and its corollaries use (Q) only through Mal'cev's theorem.
