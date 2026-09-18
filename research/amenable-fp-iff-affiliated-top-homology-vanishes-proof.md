---
rg: 2
id: amenable-fp-iff-affiliated-top-homology-vanishes-proof
kind: route
title: A contractible U(G)-complex kills cohomology with U(G)-coefficients, and over a regular ring only the top-but-one L2-homology can be nonzero without being f.g.
target: amenable-fp-iff-affiliated-top-homology-vanishes
requires: []
artifacts:
  - research/artifacts/kropholler-question-zero-divisor-split-2026-09-16.md
---

Modules are left modules. `NG` is the group von Neumann algebra with faithful normal trace `tr`,
and `U = U(G)` is the algebra of operators affiliated to `NG`. `U` is a right `Z[G]`-module through
`Z[G] ⊆ NG ⊆ U`. For a group `G`, `H_q(G; U) = Tor_q^{Z[G]}(U, Z)`.

## Imports

- **(J1) Dimension over `U`.** `U` is the Ore localization of `NG` at its non-zero-divisors, so
  `U` is flat over `NG`. There is a dimension `dim_U` on all `U`-modules, additive on short exact
  sequences and monotone on submodules and quotients, with `dim_U(U ⊗_NG M) = dim_NG(M)`. A
  finitely generated projective `U`-module of dimension 0 is zero. (W. Lück, *L²-invariants*,
  Springer 2002, Chapter 8, Theorem 8.22 and the discussion of `K_0(U)` there; recalled, section
  numbers not re-checked.)
- **(J2) Regularity.** `U` is von Neumann regular (Lück, *op. cit.*, Chapter 8). Over a von
  Neumann regular ring, every finitely generated submodule of a projective module is a direct
  summand of it, and every finitely presented module is projective (K. R. Goodearl, *Von Neumann
  regular rings*, Theorem 1.11).
- **(J3) Dimension-flatness.** If `G` is amenable then `dim_NG Tor_p^{C[G]}(NG, M) = 0` for all
  `p >= 1` and all `C[G]`-modules `M` (Lück, *op. cit.*, Theorem 6.37). If `G` is infinite then
  `dim_NG(NG ⊗_{C[G]} C) = b_0^{(2)}(G) = 0` (Lück, *op. cit.*, Theorem 6.54(8); recalled). Since `C[G]` is flat
  over `Z[G]` (resp. `Q[G]`), the same holds over `Z[G]` and `Q[G]`, with `Z` or `Q` in place of `C`.
- **(J4) Tamari.** If `G` is amenable and `k[G]` is a domain for a field `k`, then `k[G]` satisfies
  the left (and right) Ore condition (D. Tamari, Proc. ICM 1954, vol. 3). This is a standard
  statement, recalled here without a pinpoint.
- **(J5) Degrijse, proof of Theorem B after Step B1.** Let `G` be finitely generated, amenable, of
  type `FP`, with `cd G = 2`. Steps B2-B5 of Degrijse's proof (arXiv:1609.07635), recorded with
  quotes in the artifact, Section 3, show `G ≅ BS(1,m)`: B2 Euler characteristic (Bass conjecture
  for amenable groups) gives `b_1(G) >= 1`; B3 Bieri--Strebel gives an ascending HNN extension
  `G = K*_t` with finitely generated base; B4 Brown--Geoghegan and `H^2(G; Z[G]) != 0` (type `FP`)
  force `cd K <= 1`; B5 gives `K ≅ Z`. According to the quotes in the artifact, the domain hypothesis
  enters Degrijse's proof only through Theorem A, used in Step B1 to obtain type `FP`.
- **(J6) Standard homological algebra.** If `cd G = n` and `G` is of type `FP_{n-1}`, there is a
  resolution `0 → P → F_{n-1} → ... → F_0 → Z → 0` with `F_i` finitely generated free and `P`
  projective (K. Brown, *Cohomology of groups*, VIII.2.1 and VIII.4.3). If also `G` is of type
  `FP_n`, then `P` may be taken finitely generated, i.e. `G` is of type `FP` (Brown, VIII.6.1).
  A presentation `<x_1..x_d | R>` gives an exact sequence
  `Z[G]^R → Z[G]^d → Z[G] → Z → 0`, the last map sending `e_j ↦ x_j - 1` and the first given by
  the Fox Jacobian (Lyndon; Brown, II.5, Exercise 3).

## Step 1: item 1

Fix a resolution as in (J6), and write `P_•` for it.

**Lemma A.** If `H_q(G; U) = 0` for all `q`, then `H^k(G; V) = 0` for every `U`-module `V` and every
`k`.

*Proof.* `U ⊗_{Z[G]} P_•` is a bounded complex of projective `U`-modules with homology `H_q(G; U)`,
hence exact, hence split exact (a bounded-below exact complex of projectives is contractible). So
`Hom_U(U ⊗ P_•, V) = Hom_{Z[G]}(P_•, V)` is exact, and its cohomology is `H^*(G; V)`. ∎

**Lemma B.** Let `(M_i)` be a directed system of `Z[G]`-modules. Then the natural map
`lim_i H^{n-1}(G; M_i) → H^{n-1}(G; lim_i M_i)` is injective.

*Proof.* `H^{n-1}(G; M) = Z(M)/B(M)` with `Z(M) = ker(Hom(F_{n-1}, M) → Hom(P, M))` and
`B(M) = im(Hom(F_{n-2}, M) → Hom(F_{n-1}, M))` (for `n-1 = 0` put `B = 0`). Since `F_{n-1}` and
`F_{n-2}` are finitely generated, `Hom(F_{n-1}, -)` and `Hom(F_{n-2}, -)` commute with directed
colimits, so `lim B(M_i) = B(lim M_i)` and `lim Z(M_i)` is a submodule of
`Hom(F_{n-1}, lim M_i)` contained in `Z(lim M_i)`. Directed colimits are exact, so
`lim H^{n-1}(G; M_i) = lim Z(M_i) / B(lim M_i) ⊆ Z(lim M_i)/B(lim M_i)`. ∎

**Proof of item 1.** Choose a free module `F` with basis `B` and a decomposition `F = P ⊕ Q'`;
let `r : F → P` be the projection. For finite `A ⊆ B` let `⟨A⟩` be the span of `A` and
`F_A = F/⟨A⟩`, a free module. The `F_A`, ordered by inclusion of `A`, form a directed system with
surjective transition maps and `lim_A F_A = 0`.

1. The sequences `0 → F_A → U ⊗ F_A → (U/Z[G]) ⊗ F_A → 0` are exact: they are direct sums of copies of
   `0 → Z[G] → U → U/Z[G] → 0`.
2. The long exact cohomology sequence gives
   `H^{n-1}(G; (U/Z[G]) ⊗ F_A) → H^n(G; F_A) → H^n(G; U ⊗ F_A)`, and the last group is 0 by Lemma A.
3. Take colimits (exact). `lim_A (U/Z[G]) ⊗ F_A = (U/Z[G]) ⊗ lim_A F_A = 0`, so by Lemma B the colimit of the
   left-hand groups is 0. Hence `lim_A H^n(G; F_A) = 0`.
4. Since `cd G = n` and the resolution ends at `P`, `H^n(G; M) = coker(Hom(F_{n-1}, M) → Hom(P, M))`.
   Colimits are exact and `lim_A Hom(F_{n-1}, F_A) = Hom(F_{n-1}, 0) = 0`, so
   `lim_A Hom(P, F_A) = lim_A H^n(G; F_A) = 0`.
5. The compositions `π_A : P ⊆ F → F_A` form a compatible family, so some `π_A` is 0, i.e.
   `P ⊆ ⟨A⟩`. Then `P = r(P) ⊆ r(⟨A⟩) ⊆ P`, so `P = r(⟨A⟩)` is finitely generated, and `G` is of type
   `FP`. ∎

## Step 2: item 2

Let `G` be amenable with `cd G = n >= 2` and of type `FP_{n-1}`. Then `G` is finitely generated,
hence countable, and torsion-free and nontrivial (a finite nontrivial subgroup has infinite cd).
Choose the resolution of (J6) inside countable modules (`P ⊆ F_{n-1}` is then countably generated).
Put `C_• = U ⊗_{Z[G]} P_•`: `C_i ≅ U^{m_i}` for `i <= n-1`, and `C_n = U ⊗ P`.

**Dimension zero.** `C_• = U ⊗_NG (NG ⊗ P_•)` and `U` is flat over `NG`, so
`H_q(C_•) = U ⊗_NG H_q(G; NG)` and `dim_U H_q(C_•) = dim_NG H_q(G; NG) = 0` for every `q`, by (J1)
and (J3).

**Lemma D.** Over a von Neumann regular ring, a countably generated submodule `N` of a finitely
generated projective module `K` is projective.

*Proof.* Write `N = ∪_k N_k` with `N_1 ⊆ N_2 ⊆ ...` finitely generated. By (J2), `N_k` is a direct
summand of `K`, `K = N_k ⊕ E`, so by the modular law `N_{k+1} = N_k ⊕ (E ∩ N_{k+1})`. Put
`N_0 = 0` and `E_k = E ∩ N_{k+1}` for the complement of `N_k` in `N_{k+1}`. Then `N = ⊕_k E_k`, and each `E_k`
is a direct summand of the finitely generated submodule `N_{k+1}`, itself a direct summand of `K`,
so `E_k` is projective. ∎

**Lemma E.** A projective `U`-module `P'` with `dim_U P' = 0` is zero.

*Proof.* If `P' != 0`, it is a direct summand of a free module, so some coordinate map
`φ : P' → U` is nonzero; pick `x ∈ P'` with `φ(x) != 0`. By (J2), `Uφ(x)` is a nonzero finitely
generated projective module (a direct summand of `U`), so `dim_U Uφ(x) > 0` by (J1). It is a quotient of
`Ux ⊆ P'`, so `dim_U P' > 0` by monotonicity. ∎

**Degrees `q <= n-2`.** Here `C_{q+1}, C_q, C_{q-1}` are finitely generated free. The image of
`C_q → C_{q-1}` is a finitely generated submodule of a free module, hence projective by (J2), so
the kernel `Z_q` is a direct summand of `C_q`, hence finitely generated. So
`H_q(C_•) = Z_q / im(C_{q+1})` is finitely presented, hence projective by (J2), of dimension 0,
hence 0 by (J1).

**Degree `n`.** Let `J = im(C_n → C_{n-1}) ⊆ U^{m_{n-1}}`. It is countably generated because `P` is,
so `J` is projective by Lemma D. Hence `C_n → J` splits, `H_n(C_•) = ker(C_n → J)` is a direct
summand of `C_n`, and it is projective of dimension 0, hence 0 by Lemma E.

**Degrees above `n`.** `C_q = 0`.

So `H_q(G; U) = 0` for all `q != n-1`. If `H_{n-1}(G; U) = 0` too, item 1 gives type `FP`.
Conversely, if `G` is of type `FP`, take `P` finitely generated. Then `H_{n-1}(C_•)` is the quotient of a
finitely generated kernel by a finitely generated image, hence finitely presented, projective and
of dimension 0, hence 0. ∎

## Step 3: item 3

Let `G != 1` be amenable with `Z[G]` a domain. Then `Q[G]` is a domain (artifact, Remark 1.0) and
`G` is torsion-free (`(1-g)(1+g+...+g^{q-1}) = 0` for `g` of order `q`).

1. **Nonzero elements of `Q[G]` are units of `U`.** Let `0 != a ∈ Q[G]`. Since `Q[G]a ≅ Q[G]`,
   `Tor_1^{Q[G]}(NG, Q[G]/Q[G]a) = ker(NG → NG, y ↦ ya)`, which has dimension 0 by (J3). It is the
   left ideal `NG(1-p)`, where `p` is the projection onto the closure of the range of the operator
   `a`, so `tr(1-p) = 0` and `p = 1`. In a finite von Neumann algebra an operator with dense range
   has trivial kernel, so `a` is a non-zero-divisor of `NG`, and it is invertible in `U` by (J1).
2. **Localization.** By (J4), `Q[G]` is left Ore, with classical left ring of quotients `D`, a
   division ring, flat as a right `Q[G]`-module. By step 1 and the universal property of Ore
   localization, `Q[G] ⊆ U` extends to a ring map `D → U`. It is injective because `D` is a division
   ring.
3. **Acyclicity.** `U` is a `D`-module, hence flat over `D`. With `P'_•` a projective resolution of
   `Q` over `Q[G]` (for instance `Q[G] ⊗_{Z[G]} P_•`),
   `Tor_q^{Z[G]}(U, Z) = H_q(U ⊗_{Q[G]} P'_•) = U ⊗_D H_q(D ⊗_{Q[G]} P'_•) = U ⊗_D Tor_q^{Q[G]}(D, Q)`.
   This vanishes for `q >= 1` by flatness of `D`. For `q = 0`, `D ⊗_{Q[G]} Q = D / D·I_G = 0`,
   because for `g != 1` the element `g - 1` is a unit of `D`. ∎

So the vanishing in items 1-2 is implied by the domain hypothesis, and items 1-2 recover
Degrijse's Theorem A for nontrivial `G`.

## Step 4: item 4

Let `G` be finitely generated and amenable with `cd G = 2`.

- **(a) ⇒ (b).** `BS(1,m)` is finitely presented.
- **(b) ⇒ (c).** Type `FP_2` and `cd G = 2` give type `FP` (J6), and item 2 gives
  `H_1(G; U) = 0`.
- **(c) ⇒ (a).** By item 2 (with `n = 2`), `G` is of type `FP`. By (J5), `G ≅ BS(1,m)`.
- **(c) ⇔ (d).** Tensor the Lyndon sequence (J6) with `U`. `H_0(G; U) = 0` (Step 2), so
  `U^d → U` is onto and its kernel `K` is a direct summand of `U^d` (J2) of dimension `d - 1`.
  The rows of the Fox Jacobian span a submodule `J ⊆ K`, and `H_1(G; U) = K/J`. For a finite set
  `S` of relators let `J_S ⊆ J` be the span of their rows. The von Neumann rank of the corresponding
  `|S| × d` Fox matrix is `dim_U J_S`; this is the standard definition through `U`, and it agrees
  with the `NG`-dimension of the closure of the image of the `ℓ²` operator (Lück, *op. cit.*,
  Chapter 8). `J` is the directed union of the `J_S`, and `K` is finitely generated, so `J = K` if and
  only if `J_S = K` for some finite `S`. By (J2), `J_S` is a direct summand of `K`, and the complement is
  finitely generated projective of dimension `d - 1 - dim_U J_S`. So `J_S = K` if and only if
  `dim_U J_S = d - 1`, by (J1). Only amenability and finite generation are used here.

**Consequence.** Suppose every amenable group of cd at most 2 is solvable. Let `G` be finitely generated
and amenable with `cd G = 2`. Then `G` is a solvable group of cd 2, so by Gildenhuys' classification (artifact, (I8)) it is
`BS(1,m)` or a noncyclic subgroup of `Q`. Noncyclic subgroups of `Q` are not finitely generated, so
`G ≅ BS(1,m)` and (c) holds.

Conversely, suppose (c) holds for every finitely generated amenable group of cd 2, and let `G` be
amenable with `cd G <= 2`. Each finitely generated subgroup `H` has `cd H <= 2`. If `cd H = 0`,
then `H = 1`. If `cd H = 1`, then `H` is free and amenable (artifact, (I4)), so `H ≅ Z`. If
`cd H = 2`, then (c) ⇒ (a) gives `H ≅ BS(1,m)`. All of these groups are metabelian, so the law
`[[x,y],[z,w]] = 1` holds in every finitely generated subgroup, hence in `G`, and `G` is solvable. ∎

## Calibration and limits

- **`Z²`.** `<x, y | [x,y]>` has Fox row `(1 - y, x - 1)` up to units. It has von Neumann rank `1 = d - 1`, so
  (d) holds with `S` the single relator, as it must.
- **Non-amenable groups.** For the Bieri--Stallings kernel `N = ker(F_2 × F_2 → Z)` (finitely generated,
  `cd 2`, not `FP_2`), item 1 forces `H_q(N; U(N)) != 0` for some `q`. There is no conflict with item 2,
  which needs amenability through (J3).
- **Where the difficulty sits.** For amenable `G`, `H_1(G; U)` always has dimension 0. The ranks
  `dim_U J_S` increase to `d - 1`, and the question is only whether the supremum is attained. Integral ranks (strong
  Atiyah over `Q`) would force attainment. For amenable `G` that is equivalent to `Q[G]` being a
  domain, so it gives nothing new. What is new is that attainment for the *single* module `Z` is
  all that dimension 2 needs.
- **Higher dimensions.** In every dimension `n >= 2`, Degrijse's Theorem A holds with "`Z[G]` a
  domain" replaced by the weaker hypothesis `H_{n-1}(G; U(G)) = 0` (item 2 and item 3). The rest of
  Degrijse's dimension-2 argument (Euler characteristic) does not transfer to dimension 3 (artifact,
  Section 6).
