---
rg: 2
id: malnormal-coset-action-soficity-from-hyperbolic-fillings-proof
kind: route
title: Fill the stabilizer deeply in the host and in its double, read coset membership off the double's normal form, and pass to the marked-pair limit
target: malnormal-coset-action-soficity-from-hyperbolic-fillings
requires:
  - relatively-hyperbolic-dehn-filling
  - sofic-coset-actions-pass-to-marked-colimits
  - gkp-sofic-action-toolkit
---

Notation: `G` is word-hyperbolic with finite generating set, `B_R` is the
closed ball of radius `R`, and `H <= G` is quasiconvex, almost malnormal and
residually finite. Quasiconvex subgroups of hyperbolic groups are finitely
generated and hyperbolic.

## Imported theorems

- **(O) Osin's Dehn filling**, `relatively-hyperbolic-dehn-filling`
  (Osin, Invent. Math. 2007, Thm 1.1 and Cor 1.2, read verbatim on
  2026-09-11). If `X` is hyperbolic relative to a finitely generated `P`,
  then for every finite `F subset X` there is a finite `B subset P \ {1}`
  such that for every `N ⊴ P` with `N ∩ B = ∅`:
  - `P/N -> X/<<N>>` is injective;
  - `X/<<N>>` is hyperbolic relative to `P/N`;
  - the quotient map is injective on `F`;
  - if `P/N` is finite, `X/<<N>>` is word-hyperbolic.
- **(Bo)** Bowditch, *Relatively hyperbolic groups*, IJAC 22 (2012),
  Theorem 7.11. A word-hyperbolic group is hyperbolic relative to any
  almost malnormal finite family of infinite quasiconvex subgroups. Not
  re-read here.
- **(Comb)** The double `D = G *_H G` is word-hyperbolic and `H` is
  quasiconvex in `D`. Sources:
  - for `H` quasiconvex and almost malnormal: Bestvina--Feighn, *A
    combination theorem for negatively curved groups*, J. Differential Geom.
    35 (1992), whose annuli-flare hypothesis follows from almost
    malnormality plus quasiconvexity;
  - for `H` malnormal: Kharlampovich--Myasnikov, *Hyperbolic groups and
    free constructions*, Trans. AMS 350 (1998), and Gitik, *Ping-pong on
    negatively curved groups*, J. Algebra 217 (1999);
  - quasiconvexity of vertex and edge groups: I. Kapovich, *The combination
    theorem and quasiconvexity*, IJAC 11 (2001).

  An alternative to (Comb)+(Bo) for step 2 is Dahmani's combination theorem
  (*Combination of convergence groups*, Geom. Topol. 7 (2003), Thm 0.1).
  There `G` is hyperbolic relative to `H` by (Bo), and amalgamating over the
  maximal parabolic `H` gives `D` hyperbolic relative to `H`. None of these
  statements was re-read in this session. This is the trust surface.

If `H` is finite, Theorem A is GKP Theorem 2.14 (locally finite
stabilizers) applied to the sofic group `G`. The "more precisely" clause
holds with `N_R = {1}`. From now on `H` is infinite.

## Step 1. `G` is hyperbolic relative to `H`

This is (Bo) with the family `{H}`.

## Step 2. `D` is hyperbolic relative to `H`

Let `i_0, i_1 : G -> D` be the two factor inclusions, identified on `H`.
By (Comb), `D` is hyperbolic and `H = i_0(H)` is quasiconvex in `D`.

**`H` is almost malnormal in `D`.** Let `T` be the Bass--Serre tree and `e`
the edge with stabilizer `H`. Take `d in D` with `dHd^(-1) ∩ H` infinite.
That intersection fixes `e` and `de`, hence the geodesic between them.

Suppose `de ≠ e`. The geodesic contains a vertex `v` with two distinct
incident edges `e_1, e_2`. Translate `v` to a standard vertex, with
stabilizer `i_k(G)`. The edges at a standard vertex are the cosets
`i_k(gH)`, so the two edge stabilizers are `i_k(g_1 H g_1^(-1))` and
`i_k(g_2 H g_2^(-1))` with `g_1^(-1) g_2 ∉ H`. Their intersection is
conjugate to `H ∩ (g_1^(-1)g_2) H (g_1^(-1)g_2)^(-1)`, which is finite. That
contradicts infiniteness.

So `de = e`, i.e. `d in H`. By (Bo), `D` is hyperbolic relative to `H`.

## Step 3. The filling

Fix `R`. Define two finite sets:

- `F_G = B_R`;
- `F_D = {1} ∪ { w_g : g in B_R \ H }`, where `w_g = i_0(g) i_1(g)^(-1)`.

Each `w_g` is nontrivial in `D`. It is an alternating product of an element
of `i_0(G) \ H` and an element of `i_1(G) \ H`, so it is reduced of length 2
and nontrivial by the normal form theorem for amalgams.

Apply (O) to `(G,H,F_G)` and to `(D,H,F_D)`, obtaining finite sets
`B^G, B^D subset H \ {1}`. Since `H` is residually finite, there is a
finite-index normal `N = N_R ⊴ H` disjoint from `B^G ∪ B^D`. Put:

- `Gbar = G/<<N>>_G`, with quotient map `pi`;
- `Dbar = D/<<N>>_D`, with quotient map `pi_D`;
- `Hbar = H/N`.

By (O):

- `Hbar` injects into `Gbar`;
- `Gbar` is word-hyperbolic, because `Hbar` is finite;
- `pi` is injective on `B_R`, so `ker pi ∩ B_R = {1}`;
- `pi_D` is injective on `F_D`, so `pi_D(w_g) ≠ 1` for `g in B_R \ H`.

## Step 4. The filled double is the double of the filling

A homomorphism `Dbar -> Y` is a pair of homomorphisms `G -> Y` that agree
on `H` and kill `N`. Equivalently, it is a pair of homomorphisms
`Gbar -> Y` that agree on the image of `H`. That image is `Hbar`, embedded
the same way in both copies. So

```text
Dbar = Gbar *_Hbar Gbar,   pi_D(w_g) = pi(g)_0 pi(g)_1^(-1).
```

If `pi(g) in Hbar`, then `pi(g)_0 = pi(g)_1` in the amalgam and
`pi_D(w_g) = 1`. So for `g in B_R \ H`, Step 3 gives `pi(g) ∉ Hbar`. The
converse `g in H => pi(g) in Hbar` is trivial. This proves clauses 1 and 2
of Theorem A.

## Step 5. The limit

Let `p : F -> G` be a surjection from a free group on a countable set, and
enumerate `F`. Define the marked pairs

```text
(N_R, M_R) = ( p^(-1)(ker pi_R), p^(-1)(pi_R^(-1)(Hbar_R)) ).
```

For `w in F` with `p(w) in B_R`, clauses 1 and 2 give:

- `w in N_R` iff `w in ker p`;
- `w in M_R` iff `w in p^(-1)(H)`.

Every `w` has `p(w) in B_R` for all large `R`. So `(N_R, M_R)` converges
pointwise to `(ker p, p^(-1)H)`, whose coset action is `G ↷ G/H`.

The action of `F/N_R` on `F/M_R` is `Gbar_R ↷ Gbar_R/Hbar_R`, composed with
the quotient `F/N_R ≅ Gbar_R`: the map `w M_R -> pi_R(p(w)) Hbar_R` is an
equivariant bijection because `pi_R p` is onto. Assume every hyperbolic group
is sofic. Then:

- `Gbar_R` is sofic;
- `Hbar_R` is finite, so `Gbar_R ↷ Gbar_R/Hbar_R` is sofic by GKP
  Theorem 2.14;
- the action of `F/N_R` is sofic by GKP Proposition 2.15(1).

By closedness (`sofic-coset-actions-pass-to-marked-colimits`, item 6), the
limit `G ↷ G/H` is sofic. This proves Theorem A.

## Corollary B: the trivial direction

We need that the regular action of `G` is sofic only if `G` is sofic.

Use GKP Proposition 2.9: a homomorphism
`phi : G -> prod_U (S_n, d)` and `pi : G -> X_U` with
`S_U(phi(g)) pi(x) = pi(gx)` and `d_U(pi(x), pi(y)) = 1` for `x ≠ y`. Here
points of `X_U` are ultralimits of maps `[n] -> B_n`, `S(sigma)` acts by
precomposition with `sigma^(-1)`, and `d` is normalized Hamming distance.
(This reading of `X_U` is the one used in GKP's proofs. The verified
artifact records only the displayed equivalence.)

For `g ≠ 1`, put `x = 1`. The two functions `pi_n(1)` and
`pi_n(1)∘phi_n(g)^(-1)` differ at asymptotically all points of `[n]`. They
agree at every fixed point of `phi_n(g)`, so the fixed-point proportion of
`phi_n(g)` tends to 0 along `U`. Hence `phi` is a sofic embedding and `G` is
sofic.

The same argument applies to any faithful sofic action. So the forward
direction of Corollary B uses Theorem A, and the converse uses `H = {1}`
together with this remark.

## Corollary C

Apply GKP Theorems 3.6 and 3.8 with `H ↷ X` replaced by `G ↷ G/H`, which is
sofic by Theorem A. Here `G` itself is sofic by hypothesis, hence
hyperlinear. For the double, apply
`sofic-coset-action-makes-amalgam-double-sofic`. Note that `D` is
hyperbolic anyway by (Comb), so for the double this is only consistent,
not new.

## Corollary D

- Item 1 of `sofic-coset-actions-pass-to-marked-colimits`: separable
  stabilizers give sofic actions.
- Haglund--Wise (*Special cube complexes*, GAFA 2008): quasiconvex subgroups
  of virtually compact special hyperbolic groups are separable.
- Almost malnormal infinite `H` is its own commensurator. Any `g` with
  `gHg^(-1) ∩ H` of finite index in `H` has `gHg^(-1) ∩ H` infinite, so
  `g in H`.

## Model test

- **The hypotheses are not vacuous.** For every infinite-order `g` in a
  hyperbolic group, the maximal elementary subgroup `E(g)` is almost
  malnormal, quasiconvex and virtually cyclic, hence residually finite
  (`hyperbolic-group-relative-to-maximal-elementary-subgroup`).
  - So Theorem A covers `G ↷ G/E(g)`, an **amenable** stabilizer. This is
    exactly the case GKP (p. 8) could not settle. Unless `E(g)` is
    separable, no known theorem makes that action sofic.
  - In cocompact `Sp(n,1)` lattices, separability of cyclic or quasiconvex
    subgroups is not known.
- **Almost malnormality is load-bearing in the double.** Without it, `D`
  need not be hyperbolic. For `F_2 = <a,b>` and `H = <a^2>`, the double
  `F_2 *_H F_2` contains `<a^2, a_0 a_1^(-1)> ≅ Z^2`, and Osin's theorem is
  unavailable.
- **Residual finiteness of `H` is used only to make `Hbar_R` finite.** With
  an infinite hyperbolic `Hbar_R`, GKP Theorem 2.14 no longer applies. That
  case would need the non-locally-finite stabilizer case GKP left open.
