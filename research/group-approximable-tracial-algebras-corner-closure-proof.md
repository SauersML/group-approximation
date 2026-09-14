---
rg: 2
id: group-approximable-tracial-algebras-corner-closure-proof
kind: route
title: Lift the projection, round its trace, and absorb the rational amplification into a finitary symmetric group factor
target: group-approximable-tracial-algebras-closed-under-corners
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
  - group-factor-local-universality-reduces-to-ultraproducts
---

**Conventions.**  A tracial ultraproduct is
`prod_V (L_n, tau_n) = l^infinity(L_n) / {x : lim_V ||x_n||_2 = 0}`.
Contractions lift to contractions, because the quotient map is a
*-homomorphism of C*-algebras.
- Lemma M on route `locally-universal-group-factor-nonhyperlinear-proof`: moments determine embeddings.
- `S_fin` is the group of finitary permutations of `N`. It is ICC, since a
  nontrivial finitary permutation has infinitely many conjugates, so `L(S_fin)`
  is a II_1 factor.
- For a nontrivial countable group `Lambda`, `Lambda * Z` is ICC, so `L(Lambda * Z)`
  is a II_1 factor containing `L(Lambda)` trace-preservingly.
- Standard II_1 factor facts used: two projections of equal trace in a II_1
  factor are Murray--von Neumann equivalent, every projection has
  subprojections of every smaller trace and superprojections of every larger
  trace, and every II_1 factor contains a unital copy of `M_a` for every `a`.

**Lemma D' (diagonalizing iterated ultraproducts of group factors).**  If a
separable `N` embeds trace-preservingly into `(prod_V L(Gamma_n))^W`, then `N`
embeds into `prod_(V') L(Gamma'_k)` for countable groups `Gamma'_k` and a
nonprincipal ultrafilter `V'` on `N`.
*Proof.*
1. Fix contraction generators `a_1, a_2, ...` and the finite set `P_k` of
   *-monomials of degree `<= k` in `a_1..a_k`.
2. Lift twice. For each `k` there is a group `Gamma'_k` (one of the `Gamma_n`)
   and contractions `b^(k)` in `L(Gamma'_k)` whose `P_k`-moments are within
   `1/k` of those of `a`. The good index sets are in the ultrafilters, hence nonempty.
3. The tuple `[(b^(k))_k]` in `prod_(V') L(Gamma'_k)` has exactly the moments of
   `a`, and Lemma M gives the embedding.

**Item 1.**
- *Connes-embeddable algebras are in `GF`.* Every matrix algebra `M_d` embeds
  unitally and trace-preservingly into the II_1 factor `L(S_fin)`. So every
  tracial matrix ultraproduct embeds into `prod_V L(S_fin)`.
- *If every countable group is hyperlinear, `GF` is the Connes-embeddable class.*
  Let `N` embed into `prod_V L(Gamma_n)`. By direction (1) ⟹ (2) of
  `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower`, each
  `L(Gamma_n)` embeds into a tracial matrix ultraproduct. Diagonalizing as in
  Lemma D' (with matrix algebras in place of group factors) puts `N` into one
  matrix ultraproduct.
- *Otherwise `GF` is larger.* If some countable `Gamma` is not hyperlinear,
  `L(Gamma)` is in `GF` (constant sequence), and by direction (2) ⟹ (1) of the
  same node it is not Connes-embeddable.

**Item 2 (corners).**  Subalgebras are immediate. For corners, let `N` embed
into `L := prod_V L(Gamma_n)`, let `p in N` be a projection of trace `t > 0`,
and replace each `Gamma_n` by `Gamma_n * Z`; the inclusions
`L(Gamma_n) ⊆ L(Gamma_n * Z)` are trace-preserving, so now each
`L_n := L(Gamma_n * Z)` is a II_1 factor. (For `Gamma_n = 1` use `Z`.)

*Step P (lift the projection).*
- Represent `p` by self-adjoint `x_n` with `0 <= x_n <= 1` (functional
  calculus on any self-adjoint representative).
- Since `p = p^2`, `lim_V ||x_n - x_n^2||_2 = 0`.
- Put `p_n = chi_[1/2,1](x_n)`. For `s in [0,1]`,
  `|s - chi_[1/2,1](s)| <= 2|s - s^2|`: if `s >= 1/2` then `1 - s <= 2s(1-s)`,
  and if `s < 1/2` then `s <= 2s(1-s)`.
- Hence `||x_n - p_n||_2 <= 2||x_n - x_n^2||_2 -> 0`, so `(p_n)` is a sequence
  of projections representing `p`, and `tau_n(p_n) -> t` along `V`.

*Step R (round the traces).*
- Pick rationals `r_n = a_n/k_n in (0,1]` with `|r_n - tau_n(p_n)| -> 0`.
- In the II_1 factor `L_n` choose a projection `p'_n` of trace `r_n` that is a
  sub- or superprojection of `p_n`.
- Then `||p_n - p'_n||_2^2 = |tau_n(p_n) - r_n| -> 0`, so `(p'_n)` still
  represents `p`.

*Step C (compress).* Map `x = pxp` in `pNp`, with representative `(x_n)`, to
`[(p'_n x_n p'_n)]` in `prod_V (p'_n L_n p'_n, r_n^(-1) tau_n)`.
- Well defined: `r_n^(-1/2) ||p'_n y_n p'_n||_2 <= r_n^(-1/2) ||y_n||_2 -> 0`
  for null sequences, because `r_n -> t > 0`.
- A unital *-homomorphism: `p` maps to the unit.
- Trace-preserving for the normalized traces:
  `r_n^(-1) tau_n(p'_n x_n p'_n) -> t^(-1) tau(pxp)`.
- Injective, since it preserves the faithful trace.

*Step A (absorb the rational amplification).* Let `L = L(Lambda)` be a II_1
factor and `q in L` a projection of trace `a/k` with `1 <= a <= k`.
1. `x -> x ⊗ 1` embeds `(qLq, tau/tau(q))` unitally and trace-preservingly into
   `(q ⊗ 1)(L ⊗ M_k)(q ⊗ 1)` with normalized trace.
2. In the II_1 factor `L ⊗ M_k`, the projections `q ⊗ 1` and `1 ⊗ e` have
   equal trace `a/k`, where `e` is the sum of the first `a` diagonal matrix
   units. So they are equivalent through a partial isometry `v`, and
   `y -> v y v*` is a trace-preserving isomorphism onto `L ⊗ M_a`.
3. A unital copy of `M_a` inside `L(S_fin)` gives a unital trace-preserving
   embedding `L ⊗ M_a -> L ⊗ L(S_fin) = L(Lambda × S_fin)`.

Applying Step A coordinatewise to `p'_n L_n p'_n` (arbitrarily on the `V`-null
set where `p'_n` vanishes) gives unital trace-preserving embeddings into
`L((Gamma_n * Z) × S_fin)`. Their ultraproduct composed with Step C embeds
`pNp` into `prod_V L((Gamma_n * Z) × S_fin)`. So `pNp` is in `GF`.

**Item 3.**  `p_omega` is a central projection of trace `1/|J|` in
`L(Gamma)`, which lies in `GF`. Apply item 2.

**Item 4.**
- (a) ⟹ (b): a locally universal `L(U)` is itself separable and in `GF`.
- (b) ⟹ (c): if `S` is locally universal and embeds into `prod_V L(Gamma_n)`,
  every separable `N` embeds into `S^W`, hence into `(prod_V L(Gamma_n))^W`,
  and Lemma D' places `N` in `GF`.
- (c) ⟹ (a): this is direction (2) ⟹ (1) of
  `group-factor-local-universality-reduces-to-ultraproducts`.
