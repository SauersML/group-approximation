---
rg: 2
id: self-wreathing-groups-are-not-fp-infinity-proof
kind: route
title: The complement P of R wr_X P is a retract, retracts wreathe coordinatewise, and in the first nonzero degree of P the Lyndon-Hochschild-Serre sequence of W_n wr_X P has only its two edge terms, so each level adds a split copy of H_k(P)
target: self-wreathing-groups-are-not-fp-infinity
requires:
  - fully-self-replicating-tree-groups-give-fg-tits-hosts
artifacts:
  - experiments/self-wreathing-homology-2026-09-17/iterated_wreath_multipliers.g
  - experiments/self-wreathing-homology-2026-09-17/iterated_wreath_multipliers.out
  - experiments/self-wreathing-homology-2026-09-17/explicit_central_extension.g
  - experiments/self-wreathing-homology-2026-09-17/explicit_central_extension.out
---

The notation is that of the target. All homology has integer coefficients unless a field
is shown. `H_j(G)` means `H_j(G; Z)`.

## 0. The least degree `k`

`P ≠ 1` is finite. By Swan (1960, "The nontriviality of the restriction map in the
cohomology of groups"), `H^n(P; Z) ≠ 0` for infinitely many `n`. For `n ≥ 2`,
universal coefficients give `H^n(P; Z) ≅ Ext(H_{n−1}(P), Z)`, because `H_n(P)` is finite
for `n ≥ 1`. So some `H_j(P)` with `j ≥ 1` is nonzero, and `k` is well defined. In the
cases used for the Tits route `k` is explicit: `k = 1` iff `P^{ab} ≠ 1`, and `k = 2` for
`A_d` with `d ≥ 5`, whose Schur multiplier is `Z/2` (or `Z/6` for `d = 6, 7`).

## 1. Retracts (item 1)

A **retract** of `G` is a subgroup `Q` with a homomorphism `r : G → Q` restricting to the
identity on `Q`. Then `H_*(Q)` is a direct summand of `H_*(G)`, via inclusion and `r_*`.

- **The complement.** In `R ≀_X P = R^X ⋊ P`, the subgroup `1 ⋊ P` is a retract, via the
  quotient map onto `P`. Transport through the isomorphism `R ≅ R ≀_X P`: `W_1 = P` is a
  retract of `R`.
- **Wreathing.** If `(i, r)` exhibits `Q` as a retract of `G`, then
  `i^X ⋊ id : Q ≀_X P → G ≀_X P` and `r^X ⋊ id : G ≀_X P → Q ≀_X P` are homomorphisms,
  because `i^X` and `r^X` commute with the permutation of coordinates. Their composite
  is the identity. So `Q ≀_X P` is a retract of `G ≀_X P`.
- **Induction.** If `W_n` is a retract of `R`, then `W_{n+1} = W_n ≀_X P` is a retract of
  `R ≀_X P ≅ R`. Retracts of retracts are retracts. ∎

## 2. Homology of `W_n` in low degrees (item 2)

**Künneth step.** Let `A_1, …, A_m` be groups with `H_j(A_i) = 0` for `0 < j < k`. Then
`H_j(A_1 × ⋯ × A_m) = 0` for `0 < j < k`, and the inclusions of the factors induce an
isomorphism `⊕_i H_k(A_i) → H_k(A_1 × ⋯ × A_m)`.

*Proof.* Induct on `m`, using the integral Künneth sequence for `B × A`:
`0 → ⊕_{a+b=j} H_a(B) ⊗ H_b(A) → H_j(B × A) → ⊕_{a+b=j−1} Tor(H_a(B), H_b(A)) → 0`.
For `j ≤ k`, a tensor term with `a, b ≥ 1` needs `a, b ≥ k`, so `j ≥ 2k > k`; such
terms are absent. The surviving tensor terms are `H_j(B) ⊗ Z` and `Z ⊗ H_j(A)`, and they
are the images of the two inclusions. A Tor term needs `a + b = j − 1 ≤ k − 1`. So `a`
and `b` are `0` or at least `k`, which forces `a = b = 0`, and `Tor(Z, Z) = 0`. ∎

**LHS step.** Let `W` satisfy `H_j(W) = 0` for `0 < j < k`, and let `G = W^X ⋊ P`,
`N = W^X`. Then `H_j(G) = 0` for `0 < j < k`, and `H_k(G) ≅ H_k(W)^{o} ⊕ H_k(P)`.

*Proof.* Use the Lyndon--Hochschild--Serre spectral sequence
`E^2_{pq} = H_p(P; H_q(N)) ⇒ H_{p+q}(G)`.

- By the Künneth step, `H_q(N) = 0` for `0 < q < k`. So `E^2_{pq} = 0` whenever
  `0 < q < k`.
- **Low degrees.** For `0 < j < k`, the only possibly nonzero terms of total degree `j`
  are `E^2_{j,0} = H_j(P) = 0` and `E^2_{0,j} = H_j(N)_P = 0`. So `H_j(G) = 0`.
- **The row `q = 0` is permanent.** `G → P` is split by the complement. So the edge map
  `H_n(G) → H_n(P) = E^2_{n,0}` is onto, `E^∞_{n,0} = E^2_{n,0}`, and every differential
  leaving the bottom row is zero.
- **Degree `k`.** The terms of total degree `k` are `E^2_{k,0} = H_k(P)`, the zero terms
  with `0 < q < k`, and `E^2_{0,k} = H_k(N)_P`. A differential `d^r` into `E_{0,k}` starts
  at `E_{r, k−r+1}`. For `2 ≤ r ≤ k` the source row `k − r + 1` lies strictly between `0`
  and `k`, so the source is zero. For `r = k + 1` the source is in the bottom row, and
  that differential is zero. Nothing leaves `E_{0,k}`, since it lies in column `0`. So
  `E^∞_{0,k} = H_k(N)_P`.
- **The coinvariants.** By the Künneth step, `H_k(N) = ⊕_{x ∈ X} H_k(W)`, with the `x`-th
  summand the image of the `x`-th coordinate inclusion `ι_x`. For `g ∈ P`, conjugation
  satisfies `g ι_x g^{-1} = ι_{gx}`. So `P` permutes the summands without twisting, and
  `H_k(N)_P ≅ ⊕_{P-orbits} H_k(W) = H_k(W)^{o}`.
- **Assembly.** The filtration of `H_k(G)` gives `0 → E^∞_{0,k} → H_k(G) → E^∞_{k,0} → 0`,
  since the middle terms vanish. It splits by the complement. ∎

**Induction.** `W_1 = P` has `H_j = 0` for `0 < j < k` by the choice of `k`. The LHS
step applied to `W = W_n` gives the vanishing for `W_{n+1}` and
`H_k(W_{n+1}) ≅ H_k(W_n)^{o} ⊕ H_k(P)`. Since `o ≥ 1`, induction gives that
`H_k(P)^n` is a direct summand of `H_k(W_n)`. ∎

**A spectral-sequence-free check for `k = 2`.** Only the lower bound is needed in §3,
and for perfect `P` it has an explicit form. Let `W` be perfect, with a perfect central
extension `1 → A → Ŵ → W → 1`. Let `1 → Z → P̂ → P → 1` be a perfect central
extension, and let `P̂` act on `X` through `P`. Then `Ŵ ≀_X P̂` is perfect, because its
abelianization is `(Ŵ^{ab})_{P̂} ⊕ P̂^{ab} = 0`. Let `A_0 ≤ A^X` be the kernel of the
sum map `A^X → A`. It is normal, since the sum is invariant under permuting coordinates.
The quotient `(Ŵ ≀_X P̂) / A_0` maps onto `W ≀_X P` with kernel `A^X / A_0 × Z ≅ A × Z`.
This kernel is central. `A^X / A_0` is central in the base because `A` is central in
`Ŵ`, and it is fixed by the permutations. `Z` acts trivially on `X`. So `W ≀_X P` has a
perfect central extension with kernel `A × Z`, and its Schur multiplier maps onto
`A × Z`. For `P = A_5`, `Z = Z/2` (from `SL(2,5)`), and induction gives
`H_2(W_n) ↠ (Z/2)^n`, which is all that §3 uses. `explicit_central_extension.g`
builds the case `n = 2` in GAP.

## 3. The obstruction (item 3)

By §1, `H_k(W_n)` is a direct summand of `H_k(R)`, and by §2 so is `H_k(P)^n`, for
every `n`. `H_k(P)` is a nonzero finite abelian group. A finitely generated abelian group
`A` has a bound on the number of cyclic factors of any direct summand, namely the number
of cyclic factors in its primary decomposition. `H_k(P)^n` has at least `n` of them. So
`H_k(R)` is not finitely generated.

If `R` were of type `FP_k` over `Z`, there would be a projective resolution finitely
generated up to degree `k`, and `H_k(R)` would be finitely generated. So `R` is not
`FP_k`, and hence not `FP_∞`.

**Over `F_p`.** Let `p` divide `|H_k(P)|`. By universal coefficients,
`H_k(W_n) ⊗ F_p` embeds in `H_k(W_n; F_p)`, which is a direct summand of `H_k(R; F_p)`.
Its dimension is at least `n`. So `H_k(R; F_p)` is infinite-dimensional, and `R` is not
`FP_k` over `F_p`. ∎

## 4. Special cases (item 4)

- (a) `k = 1`: `H_1(R) = R^{ab}` is not finitely generated, so `R` is not finitely
  generated. `A_3 = Z/3` and `A_4` have abelianization `Z/3`.
- (b) `k = 2`: finite presentation implies `FP_2`, which fails. For `A_d` with `d ≥ 5`,
  `A_d` is perfect and has Schur multiplier `Z/2`, or `Z/6` when `d = 6, 7`.
- (c) is the statement of item 3 with `k ≥ 3`.

## 5. The Tits-route corollary

Let `R ≤ Aut(X*)` be fully self-replicating with root image `A_d`, as in
`fully-self-replicating-tree-groups-give-fg-tits-hosts`. Its proof, step (R1), shows that
every `s ∈ Aut(X*)` with root permutation in `A_d` and all sections in `R` lies in `R`.
In particular the rooted permutations, with trivial sections, form a copy of `A_d` in `R`.
The section map is an isomorphism `R ≅ R ≀_X A_d`, and it carries this copy onto the
complement. So item 4 applies. `R` is not finitely generated for `d = 3, 4`, and not
finitely presented for `d ≥ 5`. By item 4 of that node, `Γ_R` and `Γ⁺` are finitely
presented iff `R` is. So neither is ever finitely presented. ∎

## 6. The script

`iterated_wreath_multipliers.g` builds `W_n` in GAP with `WreathProduct(W_n, P)`, which is
`W_n ≀_X P` for the natural action of `P`. It prints the abelian invariants of `W_n`,
and the abelian invariants of the Schur multiplier for the perfect root images.

- `Z/3` on 3 points: `H_1(W_n) = (Z/3)^n` for `n = 1, …, 4`.
- `A_4` on 4 points: `H_1(W_n) = (Z/3)^n` for `n = 1, 2, 3`.
- `A_5`, `A_6`, `A_7`, `A_8`: perfect, with multipliers `Z/2`, `Z/6`, `Z/6`, `Z/2`.
  `A_5 ≀ A_5` is perfect.
- `M_11`: perfect with trivial multiplier, so it is outside item 4(b).
- GAP's multiplier routine exhausts its coset table on `A_5 ≀ A_5`, of order `60^6`.
  `explicit_central_extension.g` instead builds `E = SL(2,5) ≀_5 SL(2,5)`, with the top
  factor acting through `A_5` on its five Sylow 2-subgroups. GAP's `WreathProduct` puts
  the action image `A_5` on top, so `E` is built as the fibre product of
  `SL(2,5) ≀_5 A_5 → A_5 ← SL(2,5)` inside a direct product. The script checks four
  things. `E` is perfect of order `120^6`. `K = Z(SL(2,5))^5 × Z(SL(2,5)) ≅ (Z/2)^6` is
  normal with `|E/K| = 60^6`, so `E/K ≅ A_5 ≀ A_5`. The even-weight part `Z_0 ≤ (Z/2)^5`
  has order `16`. And `[E, K] = Z_0`. So `E/Z_0` is a perfect central extension of
  `A_5 ≀ A_5` with kernel `K/Z_0 ≅ (Z/2)^2`, and `H_2(A_5 ≀ A_5) ↠ (Z/2)^2`, as item 2
  predicts. No quotient group is formed, because GAP's quotient routine needs the
  `transgrp` package, which is not installed here.

## Scope

- The argument needs the complement. For groups with `R^X ⊴ R` and `R / R^X ≅ P` but no
  splitting, §1 is unavailable. Those are the non-split self-branching groups that remain
  open.
- For superperfect `P` it rules out `FP_3` at most, so finite presentation of
  `R ≅ R ≀ M_11` is not addressed.
- It says nothing about groups that are branch over a proper subgroup `K`, such as the
  Grigorchuk group. The Bartholdi--Grigorchuk--Šunić question stays open in general.
