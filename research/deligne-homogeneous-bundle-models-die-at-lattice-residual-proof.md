---
rg: 2
id: deligne-homogeneous-bundle-models-die-at-lattice-residual-proof
kind: route
title: Pin the circle parameter to order three or six with the invariant D, read the lattice section as a character that linearizes the n-fold cover of the lattice, and contradict Deligne's residual directly or through Stover's Theorem 3.3
target: deligne-homogeneous-bundle-models-die-at-lattice-residual
requires: [deligne-covers-of-sp2g-z-have-finite-residual-2z, deligne-opnorm-monomial-models-are-almost-flat-circle-bundles]
---

Notation of the target.

**Imported, verbatim.**
- From `deligne-covers-of-sp2g-z-have-finite-residual-2z` (ESTABLISHED by citation): "Let `g >= 2` and `n >= 3`.
  Let `G_n -> Sp_(2g)(R)` be the connected cover of degree `n`, `Gamma_n` the preimage of `Sp_(2g)(Z)`, and `z` a
  generator of the covering kernel `C_n = <z>`. Then ... `Gamma_n` is not residually finite, and
  `Res_fin(Gamma_n) = <z^2>`, (DR2) a cyclic group of order `n / gcd(n, 2)`." It adds: "`Gamma_n` is the quotient
  of the universal-cover preimage `Gamma~` by `<z^n>`, since `G_n = G~ / nZ`."
- From `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles` (ESTABLISHED), (L3): "`D(Lambda)` is the
  order of `z` in `H_1(Lambda~; Z)` and `Lambda~` is the preimage of `Lambda` in `Gamma~`. Moreover `D(Lambda)`
  lies in `{1, 2}` for every finite-index `Lambda`." It is used only for `Lambda = Gamma`. Its setting reads: "The
  universal-cover lattice is `Gamma~ = <S, z | [z, s] (s in S), r z^(-k_r) (r in R)>`, with `z` of infinite
  order", so its `Gamma~` and `z` are the preimage of `Gamma` in `G~` and the generator of `K_0` used here.
- From M. Stover, *Residual finiteness and discrete subgroups of Lie groups*, arXiv:2407.07680v2. The PDF was
  fetched on 2026-09-19 and pages 1-11 were read in text extraction. The same source is cited by
  `deligne-covers-of-sp2g-z-have-finite-residual-2z-citation`.
  - p. 2: "Theorem 1.2 (Malcev [19]). Let Γ be a finitely generated subgroup of GLN (C) for some N ≥ 1. Then Γ is
    residually finite."
  - p. 3, proof of Theorem 1.8: "If G is linear, then every lattice in G is finitely generated (see [13, Cor. 1.6]
    for a unified proof)".
  - p. 10: "if Γ is an irreducible lattice in a higher rank real Lie group G with finite center Z(G) and adjoint
    group G = G/Z(G), then Γ is arithmetic by famous work of Margulis [22, p. 4]. Precisely, this means that there
    is an absolutely almost simple, absolutely simply connected linear algebraic group G defined over a number
    field k and a surjection p from G(k ⊗ R) onto G with compact kernel so that the image of Γ in G is
    commensurable with the image of p(G(Ok)), where Ok is the ring of integers of k. Since G is real, k is a
    totally real number field."
  - p. 11: "Then G is said to have the congruence subgroup property if C(k) is central in ˆG(k)."
  - p. 11: "M(∅, G) is isomorphic to the dual ˆµ(k) of the group µ(k) of roots of unity of k. Since k is totally
    real, µ(k) = {±1}."
  - p. 11: "Theorem 3.3. Suppose that G is a connected semisimple Lie group with real rank at least two and Γ < G
    is an irreducible lattice with associated absolutely almost simple, absolutely simply connected algebraic
    group G defined over the totally real number field k. Let G0 denote the connected, absolutely almost simple,
    absolutely simply connected real linear algebraic group locally isomorphic to G, and suppose that G is a
    covering of G0 with degree greater than #M(∅, G) ≤ 2. If G has the congruence subgroup property, then Γ is
    not residually finite."
- Context for the hypothesis in (H3b) only, not used in any step. From G. Prasad and A. S. Rapinchuk,
  *Developments on the congruence subgroup problem after the work of Bass, Milnor and Serre*, arXiv:0809.1622v2,
  fetched 2026-09-19.
  - p. 12: "The centrality of CS(G) has been established in a large number of cases: for G = SLn and Sp 2n, in [3],
    §14, and [49], §2. ... A proof of Serre's conjecture for general isotropic groups was given by Raghunathan
    [31], [33]."
  - p. 12-13: "Martin Kneser was the first to prove the centrality of S-congruence kernel for a k-anisotropic
    group. He treated the spinor groups of quadratic forms in n ⩾ 5 variables in [12]".

**Standard facts used** (no citation node).
- `pi_1(Sp_4(R)) = Z` (Stover's p. 3 remark, quoted in the DR2 citation node). The kernel of `G~ -> G` is
  central, and `Z(Sp_4(R)) = {+-1}`.
- A discrete subgroup of a compact group is finite. The finite subgroups of `T` are the `mu_m = (1/m)Z/Z`.
- A subgroup of finite index in a finitely generated group is finitely generated, and so is an extension of a
  finitely generated group by a finite group.
- If `B <= A` has finite index and `B` is residually finite, then `A` is residually finite. (For `x != 1` outside
  `B`, use `B` itself; for `x in B`, a finite-index subgroup of `B` avoiding `x` has finite index in `A`; then take
  normal cores.) Subgroups of residually finite groups are residually finite.
- The preimage of a lattice under a finite covering of Lie groups is a lattice. A simple Lie group has only
  irreducible lattices. `Sp_4` is an absolutely almost simple, simply connected `R`-group, with real rank 2.
- `Sp_4(R) x U(1)` embeds in `GL_5(C)` as block-diagonal matrices.

## Step 0. Basics of `L_t` and the reduction to `Lambda cap T = 1`

Write `N_t = {(z^k, -k t) : k in Z}`. It is a discrete central subgroup of `G~ x T`, so `L_t` is a connected Lie
group. The map `u -> [1, u]` is injective, because `(1, u) in N_t` forces `k = 0` and then `u = 0`. Its image `T`
is central, and `L_t / T = G~ / K_0 = G`.

(0a) *Normal form.* In `L_t`, `[z^k, u] = [1, u + k t]`. Fix `g~` over `g in G`. Every element of `L_t` over `g` is
`[g~ z^k, u] = [g~, u + k t]`, so it has the form `[g~, u]`, and `u` is unique: `[g~, u] = [g~, u']` means
`(1, u - u') in N_t`, so `u = u'`. The product is `[g~, a][h~, b] = [g~ h~, a + b]`.

(0b) *Reduction.* `Lambda` is discrete and `T` is compact, so `Lambda cap T` is finite, equal to `mu_m` with
`m = |Lambda cap T|`. The homomorphism `phi_m : G~ x T -> G~ x T`, `(g~, u) -> (g~, m u)`, maps `N_t` into
`N_(mt)`. So it induces a surjection `phi_m : L_t -> L_(t')` with `t' = m t`. Its kernel consists of the
`[g~, u]` with `(g~, m u) in N_(t')`, i.e. `g~ = z^k` and `m u = -k m t`. These are the elements
`[z^k, u] = [1, u + k t]` with `m (u + k t) = 0`, i.e. exactly `mu_m <= T`. Put `Lambda' = phi_m(Lambda)` and
`rho~' = phi_m o rho~`. Then:
- `Lambda'` has the same image `Lambda_0` in `G`, and `Lambda' cap T = phi_m(Lambda cap phi_m^(-1)(T))`. Since
  `phi_m^(-1)(T) = T`, this is `phi_m(mu_m) = 1`.
- `rho~'` lifts `Gamma <= G`.
- `rho~(z)` lies over `1 in G`, so `rho~(z) = [1, r_0]` with `3 r_0 = 0`, because `z^3 = 1` in `E_3`. Since
  `rho~(z) not in Lambda`, we have `[1, r_0] not in mu_m`. So `r := m r_0 != 0`, and `rho~'(z) = [1, r]` with
  `r in {1/3, 2/3}`.

From now on we work in `L_(t')` with `Lambda'`, `rho~'` and `r`.

## Step 1. Proof of (H1)

Let `q : Gamma~ -> E_3` be the quotient map. For `g~ in Gamma~`, `rho~'(q(g~))` lies over `p(g~)`. By (0a) it is
`[g~, f_Gamma(g~)]` for a unique `f_Gamma(g~) in T`. The product rule in (0a) makes `f_Gamma : Gamma~ -> T` a
homomorphism. From `rho~'(q(z)) = [1, r] = [z, r - t']`, we get `f_Gamma(z) = r - t'`.

`T` is abelian, so `f_Gamma` factors through `H_1(Gamma~; Z)`. By (L3) with `Lambda = Gamma`, the class of `z` there
has order `D(Gamma) in {1, 2}`. Hence `2 (r - t') = 0`, i.e. `t' in {r, r + 1/2}`. With `r in {1/3, 2/3}` this gives
`t' in {1/3, 2/3, 5/6, 1/6}`. The order `n` of `t'` in `T` is 3 or 6.

## Step 2. Proof of (H2)

The projection `Lambda' -> Lambda_0` has kernel `Lambda' cap T = 1` (Step 0), so it is an isomorphism. Let
`s : Lambda_0 -> Lambda'` be its inverse. For `lambda~ in Lambda_0~`, `s(p(lambda~))` lies over `p(lambda~)`. By
(0a) it equals `[lambda~, f(lambda~)]` for a unique `f(lambda~) in T`. Since `s` and `p` are homomorphisms, the
product rule makes `f : Lambda_0~ -> T` a homomorphism. From `s(p(z)) = s(1) = [1, 0] = [z, -t']` we get
`f(z) = -t'`.

Then `f(z^k) = -k t'`, which is 0 iff `n | k`. Hence:
- `f` kills `<z^n>` and descends to `Lambda_(0,n) = Lambda_0~ / <z^n>`.
- The kernel of `(p, f) : Lambda_(0,n) -> Lambda_0 x T` consists of classes of `lambda~` with `p(lambda~) = 1`,
  i.e. `lambda~ = z^k`, and `f(z^k) = 0`, i.e. `n | k`. So it is trivial, and `(p, f)` is injective.

`Lambda_0` is a lattice in the linear group `Sp_4(R)`, so it is finitely generated (Stover, proof of Thm 1.8).
`Lambda_(0,n)` is an extension of `Lambda_0` by the finite group `<z> / <z^n>`, so it is finitely generated too.
Its image under `(p, f)` is a finitely generated subgroup of `Sp_4(R) x U(1) <= GL_5(C)`, identifying `T` with
`U(1)` via `u -> e(u)`. By Malcev (Stover, Thm 1.2) the image is residually finite. Since `(p, f)` is injective,
`Lambda_(0,n)` is residually finite. This proves (H2). Only `Lambda' cap T = 1`, i.e. `Lambda cap T` finite, was
used.

## Step 3. Proof of (H3a)

Suppose `Lambda_0` is commensurable with `Gamma^g = g Gamma g^(-1)`, and put `B = Lambda_0 cap Gamma^g`. It has
finite index in both. Write `B_n`, `(Gamma^g)_n` for the preimages in `G_n` (as for `Lambda_(0,n)`).

Choose `g~ in G~` over `g`. Conjugation `c` by `g~` is an automorphism of `G~` mapping `Gamma~` onto the preimage
of `Gamma^g`. It fixes `z`, since `K_0` is central. So it descends to an isomorphism `Gamma_n -> (Gamma^g)_n`
that fixes `z`. By (DR2), for `n in {3, 6}` (so `n >= 3`), `Res_fin((Gamma^g)_n) = <z^2>`. This group is nontrivial,
since `z^2` has order `n / gcd(n, 2) = 3` for both values of `n`, so `(Gamma^g)_n` is not residually finite.

`B_n` has finite index in `(Gamma^g)_n`, since the index equals `[Gamma^g : B]`. By the standard fact on
finite-index subgroups, `B_n` is not residually finite. But `B_n <= Lambda_(0,n)`, which is residually finite by
(H2), and subgroups of residually finite groups are residually finite. This is a contradiction, so no homogeneous
model exists over such `Lambda_0`.

## Step 4. Proof of (H3b)

Let `Lambda_0` be any lattice in `G = Sp_4(R)`, and let `n in {3, 6}` be as in (H1).
- `G_n = G~ / <z^n>` is a connected simple Lie group of real rank 2. Its center is the preimage of
  `Z(Sp_4(R)) = {+-1}`, of order `2n`, so it is finite. Its adjoint group is `PSp_4(R)`.
- `Lambda_(0,n)` is the preimage of `Lambda_0` under the degree-`n` covering `G_n -> G`, so it is a lattice in
  `G_n`, and it is irreducible because `G_n` is simple.
- By the Margulis passage (Stover p. 10), `Lambda_(0,n)` is arithmetic, with an associated absolutely almost
  simple, absolutely simply connected group `H` over a totally real field `k`.
- In Stover's Theorem 3.3 take `G := G_n` and `Γ := Lambda_(0,n)`. The group `G0` is `Sp_4(R)`, the real points of
  the connected, absolutely almost simple, simply connected real group `Sp_4`, which is locally isomorphic to
  `G_n`. `G_n` covers it with degree `n >= 3`. By the p. 11 passage, `#M(empty, H) = |mu(k)| = 2`, so the degree is
  greater than `#M(empty, H)`.
- Under the hypothesis that `H` has the congruence subgroup property, Theorem 3.3 says `Lambda_(0,n)` is not
  residually finite.

This contradicts (H2). So, under CSP for `H`, no homogeneous model exists over `Lambda_0`.

**Consequence for compact quotients.** A homogeneous continuous untwisting in the sense of the target's Setting is
a homogeneous model over a cocompact `Lambda_0`. So it is excluded unconditionally when `Lambda_0` is commensurable
with a conjugate of `Sp_4(Z)` (that class contains no cocompact lattice, so for compact `K` it gives nothing) and,
under CSP, for every cocompact `Lambda_0`.

## Remark (not used). Every circle extension of `Sp_4(R)` is some `L_t`

Let `L` be a connected Lie group with a central circle `T` and `L / T = Sp_4(R)`.
- The Lie algebra is `l = sp_4(R) + R` as a central extension. Since `H^2(sp_4; R) = 0` (Whitehead), it splits, and
  `[l, l]` is isomorphic to `sp_4(R)`.
- The simply connected group `G~` integrates `[l, l] -> l` to a homomorphism `j : G~ -> L`. Then
  `(g~, u) -> j(g~) u` is a surjection `G~ x T -> L`, surjective because its image is open and `L` is connected.
- The kernel is discrete, and it projects injectively to `G~`, onto a subgroup of the kernel of `G~ -> Sp_4(R)`.
  Since `j(K_0) <= T`, that projection is all of `K_0`, and the kernel is `{(z^k, -k t)}` with `j(z) = [1, t]`
  (written additively).

So `L = L_t`. This shows that the target's standing choice of `L` loses nothing among circle extensions of
`Sp_4(R)`. It is recorded as a sketch only; the target does not depend on it.
