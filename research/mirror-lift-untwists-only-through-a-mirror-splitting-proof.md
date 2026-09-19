---
rg: 2
id: mirror-lift-untwists-only-through-a-mirror-splitting-proof
kind: route
title: Separate mirror cosets by the null-coset lemma, remove the Q-part of an untwisting map by weak mixing, kill the homomorphism on the finitary group through its positive-measure fixed sets, and lift along a treeing on treeable pieces
target: mirror-lift-untwists-only-through-a-mirror-splitting
requires:
  - bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
---

Notation as in the target and in `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift` (cited as [BL]).

**Imported facts.**
* **(N1)** The null-coset lemma, [BL] Theorem 1. Let `M` be a finite-band Toeplitz-plus-finite matrix on `X_+-` with
  `sigma(M) != 0`. Then `{x : Mx in V_fin}` is null.
* **(N2)** The symbol map `sigma : Ê_+- -> Q` is onto, with kernel the finitary group `L_+-`
  ([BL] Theorem 1, and (MQ3) of `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`).
  * Here `L_+ = GL_fin`, acting through transposes of finitary matrices on the basis `N x {1..n}`.
  * `L_+` contains the full group `SL_m(F_2)` of every initial block of `m` basis vectors.
* **(N3)** `s` is a strict cocycle on an `R_n`-invariant conull Borel set `X_0 ⊆ X_+`.
  * By (N1), the set of `x` with `Mx = M'x` and `sigma(M) != sigma(M')` is null, for each of the countably many pairs
    `(M, M')`.
  * `R_n` is the orbit relation of a countable group, so the saturation of this null set is null. Its complement is
    `X_0`.

## 1. `N_-` is a closed subgroup of a full group (Theorem part 1)

**Distinct cosets are at distance 1.** Let `f, g in N_-` with `pi_-(f) != pi_-(g)`. Write `g^(-1) f = k t` with
`k in Ê_-`, `q = sigma(k) != 1`, and `t in [T_-]`.
* If `x in Fix(kt)`, put `z = tx`. Then `z - x in V_fin` and `kz = x`, so `(k - 1) z = x - z in V_fin`.
* The matrix `k - 1` is finite-band Toeplitz-plus-finite with `sigma(k - 1) = q - 1 != 0`. By (N1),
  `Z = {z : (k-1) z in V_fin}` is null.
* So `Fix(kt) ⊆ t^(-1)(Z)` is null, because `t` preserves `mu_-`. Hence `d(f, g) = 1 - mu_-(Fix(g^(-1) f)) = 1`.

**Closedness.** `N_- ⊆ [R_-]`, where `R_-` is the orbit relation of `Ê_-` on `X_-`.
* `Ê_- ⊆ [R_-]` by definition.
* `[T_-] ⊆ [R_-]`, because `T_- ⊆ R_-` a.e. Let `v in V_fin^-`, and let `x` be a point with infinitely many nonzero
  coordinates (a.e. `x` is one).
  * Pick a coordinate `j` outside `supp(v)` with `x_j = 1`, and put `F = v e_j^T`.
  * Then `F^2 = 0` and `(1 + F) x = x + v`.
  * `1 + F` is a finitary transvection, so it lies in `L_- ⊆ Ê_-`.

Next:
* `[T_-]` is closed in `([R_-], d)`. If `d(f_j, f) -> 0` with `f_j in [T_-]`, pass to a subsequence with summable
  distances. By Borel--Cantelli, a.e. `x` has `fx = f_j x ∈ [x]_(T_-)` for large `j`.
* So each coset `f[T_-]` is closed.
* A `d`-Cauchy sequence in `N_-` eventually stays in one coset, by the distance-1 separation. So its limit lies in that
  closed coset, and `N_-` is closed in `[R_-]`.

**Finite type.** `f -> u_f` embeds `[R_-]` in `U(L(R_-))`, with `||u_f - u_g||_2^2 = 2 d(f, g)`.
* `([R_-], d)` is complete, so the image is closed.
* So `N_-` is a closed subgroup of the unitary group of the finite von Neumann algebra `L(R_-)`, which has separable
  predual. That is Popa's class `U_fin`. ∎

## 2. Weak mixing of `Ê_+ ↷ X_+`

The characters of `X_+` are `chi_v(x) = (-1)^(x(v))` for `v in V_+`.
* For `M : x -> x o h^(-1)` we get `chi_v o M = chi_(h^(-1) v)`.
* So the Koopman representation on `L^2_0(X_+)` is the permutation representation on `Omega = V_+ \ {0}`.

**Lemma 2.1.** A permutation representation `l^2(Omega)` has a nonzero finite-dimensional invariant subspace only if
some orbit in `Omega` is finite.

*Proof.* Let `P` be the projection onto such a subspace `W`.
* The kernel `K(w, w') = <P delta_(w'), delta_w>` lies in `l^2(Omega x Omega)`, since `P` is finite rank.
* `K` is invariant under the diagonal action and is nonzero, since `trace P = sum_w K(w,w) > 0`.
* An invariant `l^2` function is constant on diagonal orbits. So it is nonzero only on finite ones.
* The first projection of a finite diagonal orbit is a finite orbit in `Omega`. ∎

**Every orbit is infinite.** Let `v != 0` be supported in the first `m` basis vectors, and take `m' >= max(m, 3)`.
* By (N2), `SL_(m')(F_2) <= L_+` acts transitively on the nonzero vectors of the first `m'` basis vectors.
* So the orbit of `v` has at least `2^(m') - 1` elements, for every `m'`.

Hence `Ê_+ ↷ X_+` has no nonzero finite-dimensional invariant subspace of `L^2_0`. It is weakly mixing, and in
particular ergodic.

**Positive fixed sets.** For `M = (x -> x o h^(-1))` with `h in L_+`, `Fix(M)` is the annihilator of the subspace
`(h^(-1) - 1) V_+`.
* This subspace has finite dimension `r`.
* So `mu_+(Fix M) = 2^(-r) > 0`.

## 3. Untwisting forces a splitting (Theorem part 2)

Let `beta` be an (ML) witness. Put `alpha = alpha_beta`, so `alpha(M, x) = beta(x, Mx)`. Then:
* `alpha` is a cocycle over `Ê_+ ↷ X_+`;
* `pi_- alpha(M, x) = s(x, Mx) = sigma(M)` on `X_0`;
* `alpha(M, x) = beta(x, x) = 1` whenever `Mx = x`.

Assume (SR_beta): `alpha(M, x) = phi(Mx) rho'(M) phi(x)^(-1)` a.e., for each of the countably many `M`.

**Step 1 (removing the Q-part).** Put `phibar = pi_- o phi : X_+ -> Q` and `rhobar = pi_- o rho'`.
* Applying `pi_-` gives `phibar(Mx) = sigma(M) phibar(x) rhobar(M)^(-1)` a.e.
* Let `Ê_+` act on the countable set `Q` by `M . q = sigma(M) q rhobar(M)^(-1)`. Then `phibar` is equivariant.
* Put `A_q = phibar^(-1)(q)`. Then `M^(-1) A_q = A_(M^(-1) . q)` up to null sets. So `mu_+(A_q)` is constant along
  orbits, and since `sum_q mu_+(A_q) = 1`, every orbit `O` with `mu_+(A_q) > 0` is finite.
* Fix such an `O`. `W = span{1_(A_q) : q in O}` is a finite-dimensional invariant subspace.
  * It contains the invariant function `1_(A_O)`, which is a.e. constant by ergodicity, hence equal to `1`.
  * By weak mixing (Section 2), `W ⊖ C1` is finite-dimensional, invariant and inside `L^2_0`, so it is `0`.
* So every `1_(A_q)` is constant: `phibar = q_0` a.e. for a single `q_0`, and `O = {q_0}`. Evaluating at such points,
  `sigma(M) = q_0 rhobar(M) q_0^(-1)` for every `M`.

Pick `f_0 in N_-` with `pi_-(f_0) = q_0`, and put `psi = phi f_0^(-1)` and `rho'' = f_0 rho' f_0^(-1)`. Then:
* `alpha(M, x) = psi(Mx) rho''(M) psi(x)^(-1)` a.e.;
* `pi_- o rho'' = sigma`;
* `pi_- o psi = 1`, so `psi` takes values in `[T_-]`.

**Step 2 (killing the finitary group).** Let `M in L_+`.
* By Section 2, `Fix(M)` has positive measure, so it meets the conull set where the untwisting identity holds.
* At such an `x`: `1 = alpha(M, x) = psi(x) rho''(M) psi(x)^(-1)`, so `rho''(M) = 1`.

Hence `rho''` kills `L_+ = ker sigma` (N2). Since `sigma` is onto, it descends to a homomorphism `rho : Q -> N_-` with
`rho o sigma = rho''`. From `pi_- o rho'' = sigma` we get `pi_- o rho = id_Q`. This is (HS).

**Step 3 (the cohomology).** For `(x, y) in R_n` with `y = Mx`:

`beta(x, y) = alpha(M, x) = psi(y) rho(sigma(M)) psi(x)^(-1) = psi(y) rho(s(x, y)) psi(x)^(-1)`.

This holds a.e., because `R_n` is the countable union of the graphs of the `M`. ∎

**Converse.** If `rho` is as in (HS), then `beta = rho o s` is a cocycle, because `s` is one on `X_0`. And
`pi_- o beta = s`. So (HS) implies (ML). With Step 2 this gives: under (SR), (ML) iff (HS).

## 4. Treeable subrelations (Theorem part 3)

Let `R_0 <= R_n` be a treeable Borel subrelation. Restrict to an `R_0`-invariant conull Borel set inside `X_0` that
carries a Borel treeing `G`: an acyclic Borel graph whose components are the `R_0`-classes.
* Fix a Borel linear order `<` on `X_+`, and a set-theoretic section `q -> f_q` of `pi_- : N_- -> Q`. The group `Q`
  is countable, so no measurability issue arises.
* On edges of `G` put `b(x, y) = f_(s(x,y))` if `x < y`, and `b(x, y) = f_(s(y,x))^(-1)` if `y < x`.
  * Then `b(y, x) = b(x, y)^(-1)`.
  * And `pi_- b(x, y) = s(x, y)`, because `s(y, x) = s(x, y)^(-1)`.
* For `(x, z) in R_0`, let `x = x_0, x_1, ..., x_k = z` be the unique reduced `G`-path. Put
  `b(x, z) = b(x_(k-1), x_k) ... b(x_0, x_1)`.
  * The path is a Borel function of `(x, z)` on each Borel piece `{dist_G(x, z) = k}`, so `b` is Borel.
  * The path from `x` to `z` is the reduction of the concatenation of the paths from `x` to `y` and from `y` to `z`.
    Backtracking pairs contribute `b(y', x') b(x', y') = 1`. So `b(x, z) = b(y, z) b(x, y)`.
  * By the cocycle identity for `s`, `pi_- b = s` on all of `R_0`.

Amenable subgroups:
* If `H <= Ê_+` is amenable, its orbit relation is amenable. It is hyperfinite by Connes--Feldman--Weiss, and hence
  treeable (Kechris--Miller, *Topics in orbit equivalence*, LNM 1852: hyperfinite relations are treeable).
* The subgroup generated by `x_12(S), x_12(T), x_23(S), x_23(T)` lies in `UT_3(J)`. There `[x_12(a), x_23(b)] = x_13(ab)`
  is central, so `UT_3(J)` is nilpotent of class 2.
* So the corner test of `jacobson-haar-relation-lifts-into-bilateral-relation` always succeeds. ∎

## 5. Remarks, not part of the theorem

* **Why part 3 does not globalize.** A cocycle on `R_n` is not determined freely on a generating graphing, because
  `R_n` is not treeable. It is Kazhdan (`jacobson-haar-relation-is-kazhdan-and-unsplittable`). The whole content of
  (ML) is compatibility along the cycles of a graphing.
  * The two half-subrelations (preimages of `EL_n(F_2[x])` and `EL_n(F_2[x^(-1)])`) already lift, through the
    homomorphic half-sections recorded on `jacobson-haar-relation-lifts-into-bilateral-relation`.
  * The Steinberg relator `rho_-` is the first cycle whose compatibility is not automatic.
* **Candidate invariant for refuting (HS).** Take the commuting pair `(u_a, h^k)` of
  `jacobson-symbol-sequence-does-not-virtually-split`, mirrored to `Ê_-`. A splitting gives a measure-preserving
  involution `u'` and an automorphism `h'`, with `u' h' = h' u'`, `u' in u~[T_-]` and `h' in h~[T_-]`.
  * Let `F` be the sigma-algebra of `u'`-invariant sets. Then `h' F = F` exactly.
  * In the linear case (`u' = u~`, `h' = h~`), `F` is generated by the characters of `X_-` fixed by `u~`. `h~` moves
    it to a commensurable sigma-algebra.
  * The relative-entropy index `H(h~F | F) - H(F | h~F)` is then the natural measure-theoretic shadow of the
    Fredholm index `-k` of that node. This identification is not proved here.
  * **Where it can fail.** For `t in [T_-]` with unbounded displacement, `H(tF | F)` can be infinite. The index is
    then undefined, and it is not continuous in the uniform topology.
  * So refuting (HS) needs either a bound on the displacement of some splitting (which a splitting need not have), or
    an index that survives unbounded tail corrections.
