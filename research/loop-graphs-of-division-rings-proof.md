---
rg: 2
id: loop-graphs-of-division-rings-proof
kind: route
title: Separating edges by Cohn coproducts, non-separating edges by the infinite cyclic cover and the shift on the universal field of fractions
target: compatible-graphs-of-groups-with-loops-embed-in-division-rings
requires: []
---

## Imported tools

The source for (T1) and (T2) is S. P. Fisher and P. Sanchez-Peralta, arXiv:2303.08165v4, Section 3. Its TeX
source was read on 2026-09-17: Definition of D-compatible, Dicks normal form theorem (label `thm:NF`), Proposition `prop:kGinjects`, Theorem
`thm:graphOfHF`. The printed numbers were not checked.

- **(T1) Normal form** (Dicks, J. Algebra 81 (1983), Theorem 34(i); Cohn 1959). Let `B, C` be rings with a common
  subring `A`, with `B` free as a left `A`-module on `{1} ⊔ X` and `C` free on `{1} ⊔ Y`. Then `B *_A C` is a free
  left `B`-module on the alternating strings `y_1 x_1 y_2 x_2 ...` (`x_i in X`, `y_i in Y`) that do not begin with
  an element of `X`, the empty string included. Over a division subring `A` every module is free, and any left
  `A`-independent set containing `1` extends to such a basis.
- **(T2) Semifirs** (Cohn, J. Algebra 8 (1968); Cohn, *Free Rings and Their Relations*, §1.1 Ex. 3). A coproduct
  of two semifirs over a common division subring is a semifir. A directed union of semifirs is a semifir. Division
  rings are semifirs.
- **(T3) Universal field of fractions** (Cohn, *Free Ideal Rings and Localization in General Rings*, CUP 2006,
  §7.5). A semifir `R` has a universal field of fractions `U(R)`, which is unique up to `R`-isomorphism, and
  `R -> U(R)` is injective.
- **(T4) Ore** (Ore, Goldie). A skew Laurent ring `U[t^(±1); theta]` over a division ring `U`, with `theta` an
  automorphism, is a left and right principal ideal domain. It is therefore an Ore domain and embeds in a division
  ring.

## Step 0 (the tower lemma)

Suppose `E <= F <= G` are groups and `k[G] -> Q` sits in a division ring, with `k[F] -> D_F -> Q` and
`k[E] -> D_E -> D_F` extending. Suppose `S` is a right transversal of `E` in `F`, left independent over `D_E`, and
`T` is a right transversal of `F` in `G`, left independent over `D_F` in `Q`. Then `ST` is a right transversal of
`E` in `G`, left independent over `D_E` in `Q`.

*Proof.* Take `sum_(s,tau) d_(s,tau) s tau = 0` with `d_(s,tau) in D_E`. Collect the terms by `tau`. Each inner sum
`sum_s d_(s,tau) s` lies in `D_F`, so it vanishes by independence of `T`. Then `d_(s,tau) = 0` by independence of
`S`. ∎

Also, if `D_v -> Q` extends `k[G_v] -> D_v` and `H <= G_v`, then `Div(k[H], Q) = Div(k[H], D_v)` (as images). So
compatibility data computed inside a vertex ring is unchanged inside any larger ring.

## Step 1 (separating edge)

Let `Gamma` be finite, and suppose the theorem with (P) holds for the two components `Gamma_1 ∋ o(e)` and
`Gamma_2 ∋ t(e)` of `Gamma \ e`, with division rings `Q_1`, `Q_2`.

- By (P) and the remark in Step 0, `Div(k[G_e], Q_2) = D_e` and `Div(k[G_e], Q_1) ≅ D_ebar`. These are
  `k[G_e]`-isomorphic by compatibility (3).
- By compatibility (2), (P) and Step 0, right transversals `S_1` of `G_e` in `G_(Gamma_1)` and `S_2` of `G_e` in
  `G_(Gamma_2)` are left independent over `D_e` in `Q_1`, `Q_2`. Take `1 in S_i`.
- Put `R = Q_1 *_(D_e) Q_2`. By (T2) it is a semifir. Put `Q = U(R)` by (T3).
- Extend `S_i` to left `D_e`-bases of `Q_i`. By (T1), the alternating words `W` in `S_2 \ 1` and `S_1 \ 1` that do not
  begin in `S_1` are left `Q_1`-independent in `R`.
- `W` is a right transversal of `G_(Gamma_1)` in `G = G_(Gamma_1) *_(G_e) G_(Gamma_2)` (Serre, *Trees*, I.1
  normal form). Hence `k[G] = ⊕_(w in W) k[G_(Gamma_1)] w` maps injectively into `⊕_w Q_1 w ⊂ R ⊂ Q`.
- (P) for `v in Gamma_1`: a relation over `D_v` among `T_v W` holds in `R`, since the coefficients and the group
  elements lie in `R` and `R -> Q` is injective. Step 0 with `T_v` from (P) for `Gamma_1` kills it.
- (P) for `v in Gamma_2` is symmetric.

This is Fisher--Sanchez-Peralta Proposition 3.12. The only change is that the ambient ring is `U(R)` rather than
`R`, which (T3) allows.

## Step 2 (one non-separating edge over one vertex)

Let `A` be a group with `k[A] -> D_A`, and let `C <= A` with an injective homomorphism `phi : C -> A`. Put
`H = <A, t | t c t^-1 = phi(c), c in C>`. Assume the HNN data are compatible:
- `D_C := Div(k[C], D_A)` and `D_phiC := Div(k[phi C], D_A)` are isomorphic through `phi`;
- right transversals of `C` and of `phi(C)` in `A` are left independent over `D_C`, respectively `D_phiC`.

**The line of groups.**
- Let `N = ker(H -> Z)`, with `t -> 1` and `A -> 0`. Put `A_i = t^i A t^-i`.
- By Bass--Serre theory (the infinite cyclic cover of the one-loop graph of groups), `N` is the fundamental group
  of the bi-infinite line with vertex groups `A_i`. The edge from `i` to `i+1` has edge group
  `C_(i+1) := t^(i+1) C t^-(i+1) = t^i phi(C) t^-i <= A_i ∩ A_(i+1)`.
- Put vertex rings `D_i` := a copy of `D_A`, with `k[A_i] -> D_i` given by `x -> t^-i x t^i` followed by
  `k[A] -> D_A`.
  - Inside `D_(i+1)` the edge closure is a copy of `D_C`. Inside `D_i` it is a copy of `D_phiC`.
  - The identification between the two is the conjugation by `t`, which is `phi` on `C`.
- So the compatibility (3) of the line is the HNN hypothesis, and (2) is the transversal hypothesis. The line is
  D-compatible.

**The semifir of the line.**
- Let `R_n` be the iterated coproduct `D_-n *_(D_e) ... *_(D_e) D_n` over the edge division rings.
- By (T2) each `R_n` is a semifir. By (T1) each `R_n -> R_(n+1)` is injective.
- `R := union R_n` is a semifir by (T2).
- Run Step 1 on the segments `[-n, n]` (finite trees), adding one end vertex at a time, but with the ambient ring
  kept equal to the plain coproduct `R_n` rather than `U(R_n)`. The argument is unchanged: (T1) is applied in
  `R_[a,b+1] = R_[a,b] *_(D_e) D_(b+1)`, and the independence needed in `R_[a,b]` comes from the induction and
  Step 0. This gives:
  - injective maps `k[N_n] -> R_n` compatible with `n`, where `N_n` is the segment group and `N = union N_n`;
  - right transversals `W_n` of `A_0` in `N_n`, left independent over `D_0` in `R_n`.
- Take the `W_n` increasing. This is possible because (P) holds for any transversal once it holds for one:
  changing representatives multiplies by units of `A_0 ⊂ D_0`.
- Hence `k[N] -> R` is injective, and `W := union W_n` is a right transversal of `A_0` in `N`, left independent over
  `D_0` in `R`.

**The shift.**
- The shift `D_i -> D_(i+1)` (identity on the copies of `D_A`) respects the edge identifications, by construction.
- By the universal property of coproducts it induces an automorphism `sigma` of `R`, with inverse the backward
  shift.
- On `k[N]`, `sigma` is conjugation by `t`.

**Extending to U.**
- Let `U = U(R)` with `iota : R -> U`.
- The pair `(U, iota ∘ sigma)` is again an epic `R`-field. It is universal: specialisations from it to an
  `R`-field `(E, f)` are specialisations from `(U, iota)` to `(E, f ∘ sigma^-1)`.
- By uniqueness in (T3) there is an isomorphism `theta : U -> U` with `theta ∘ iota = iota ∘ sigma`.

**The embedding.**
- `H = N ⋊ <t>`, so `k[H] = k[N][t^(±1); conj_t]`.
- The map `sum n_j t^j -> sum iota(n_j) t^j` into `U[t^(±1); theta]` is a ring homomorphism, because `theta`
  extends `conj_t` on `k[N]`.
- It is injective coefficientwise.
- By (T4), `U[t^(±1); theta]` sits in a division ring `Q`.

**(P) for H.**
- `D_A = D_0 ⊂ R ⊂ U ⊂ Q`.
- `{w t^j : w in W, j in Z}` is a right transversal of `A` in `H`.
- A relation `sum d_(w,j) w t^j = 0` with `d_(w,j) in D_A` has, in each degree `j`, a relation
  `sum_w d_(w,j) w = 0` in `U`, hence in `R`. So all `d_(w,j) = 0`.

## Step 3 (finite graphs)

- Choose a maximal tree `Y ⊂ Gamma`. Steps 1 and induction on the edges of `Y` give `Q_Y` with (P) for all
  vertices.
- Add the remaining edges `e_1, ..., e_r` one at a time. At stage `j` the current group `A = G_(j-1)` has division
  ring `Q_(j-1)` with (P) for all original vertices.
- For the edge `e_j`, the subgroups `G_(e_j) -> G_(t(e_j)) <= A` and `G_(e_j) -> G_(o(e_j)) <= A` have closures in
  `Q_(j-1)` equal to `D_(e_j)` and `D_(ebar_j)` (Step 0 remark). These are `k[G_(e_j)]`-isomorphic by (3).
- Their transversals in `A` are left independent over these closures, by (2), (P) and Step 0.
- So Step 2 applies and gives `Q_j` with (P) for `A`, hence for every original vertex by Step 0.
- `G = G_r` (Serre, *Trees*, I.5).

## Step 4 (infinite graphs)

- `G` is the directed union of the fundamental groups `G_F` of the finite connected subgraphs `F`, which are
  D-compatible with the same data. Let `Q_F` be division rings containing `k[G_F]`.
- Choose an ultrafilter `u` on the set of finite connected subgraphs that contains every tail `{F : F ⊇ F_0}`.
  The tails have the finite intersection property.
- Map `x in k[G]` to the class of `(x_F)` in `prod_u Q_F`, where `x_F = x` when `x in k[G_F]` and `x_F = 0`
  otherwise.
- Sums and products agree on a tail, so this is a ring homomorphism. A nonzero `x` is nonzero on a tail, so it is
  injective.
- An ultraproduct of division rings is a division ring (Łoś).

## Calibration

- **Z^2.** `Z^2 = Z *_Z` with `A = C = Z` and `phi = id`. Take `D_A = k(x)`. Step 2 gives `k(x)[t^(±1)]` inside
  `k(x,t)`.
- **Tree case.** The tree case recovers the source's Proposition 3.12.
- **A mapping torus of a free group.** For `A = F_2` and `C = A` with `phi` an automorphism, Step 2 is the usual
  `D_(F_2)[t^(±1); phi]` construction.
