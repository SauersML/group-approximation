---
rg: 2
id: two-variable-kun-thom-actor-atiyah-proof
kind: route
title: Specialize the variables to independent p-adic units, then split off the free congruence quotient
target: two-variable-kun-thom-actor-satisfies-strong-atiyah
requires:
  - char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup
  - p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
  - strong-atiyah-passes-to-locally-indicable-extensions
---

Notation as in `two-variable-kun-thom-actor-satisfies-strong-atiyah`.

## Step 1: K is a subgroup of CS(1, r, p)

* **Independent units.** `1 + pZ_p` is uncountable. The elements algebraic over
  `Q(u_1)` form a countable set. So there are `u_1, u_2 in 1 + pZ_p`
  algebraically independent over `Q`.
* **Injective specialization.** Let `psi: R -> Z_p` be the ring homomorphism
  with `psi(x_i) = u_i`, well defined because the `u_i` are units. If
  `psi(f) = 0` for a Laurent polynomial `f != 0`, then `x_1^a x_2^b f` is a
  nonzero polynomial vanishing at `(u_1, u_2)`, contradicting independence. So
  `psi` is injective, and so is the induced `GL_r(R) -> GL_r(Z_p)`.
* **Congruence.** Let `M in K`. Each entry `f` has integer coefficients and
  `u_i, u_i^-1 = 1 mod p`, so `psi(f) = f(1,1) mod p`. Hence
  `psi(M) = M(1) = I mod p`.
* **Conclusion.** So `psi(K) <= CS(1,r,p) = {M in Mat_r(Z_p) : M = I mod p}`.
  For odd `p` this is a torsion-free compact `p`-adic analytic group; the node
  `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah` lists
  `Gamma(p) <= CS(1,d,p)` as an instance. Item 1 of that node gives Strong
  Atiyah over `C` for the abstract subgroup `psi(K) ≅ K`.

## Step 2: the quotient is free

* `K` is normal in `H`, with `H/K ≅ Gamma_2(p)`. `H` is torsion-free by
  `char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup`.
* `Gamma_2(p)` is torsion-free for `p >= 3` (Minkowski). It meets `{+-I}`
  trivially, so it maps injectively into `PSL_2(Z) ≅ Z/2 * Z/3`.
* In the Bass--Serre tree of that free product the vertex stabilizers are
  conjugates of `Z/2` and `Z/3`. The torsion-free image meets them trivially, so
  it acts freely and is a free group. Free groups are locally indicable.

## Step 3: Strong Atiyah for H

`K` is a torsion-free normal subgroup of `H` satisfying Strong Atiyah over `C`,
and `H/K` is locally indicable. `strong-atiyah-passes-to-locally-indicable-extensions`
gives Strong Atiyah over `C` for `H`.

**Domain consequence.** Suppose `alpha beta = 0` in `k[H]` with `char k = 0`.
The coefficients generate a finitely generated subfield, which embeds in `C`.
In `C[H]` with `H` torsion-free, Strong Atiyah makes `r_alpha` either zero or
injective on `l^2(H)`. If `alpha != 0`, then `r_alpha` is injective and
`beta = 0`. This proves item 1.

## Step 4: the compression pattern (r >= 3)

* **Property (T).** `EL_r(Z[x_1, x_2])` has property (T) for `r >= 3`. This is
  Ershov--Jaikin-Zapirain for elementary groups over finitely generated rings,
  recorded as this program's Kazhdan input in `el-r-polynomial-robust-spectral-gap`.
  It was not re-read in this lane.
  - `Gamma_0` is the kernel of a homomorphism from that group to the finite group
    `GL_r(F_p)`, so it has finite index and inherits (T).
  - It is infinite, since it contains `e_12(p x_1^n)` for all `n`.
* **Compression.** If `A` has nonnegative entries, then `alpha_A` maps
  `Z[x_1, x_2]` into itself. So `alpha_A(EL_r(Z[x_1,x_2])) <= EL_r(Z[x_1,x_2])`.
  Evaluation at `x = 1` commutes with `alpha_A`, so `alpha_A(K) = K`. Hence
  `A Gamma_0 A^-1 = alpha_A(Gamma_0) <= Gamma_0`.
* **Strictness.** `alpha_(A_1)` sends `x_1 -> x_1` and `x_2 -> x_1^p x_2`. Its
  image ring `S_1 = Z[x_1, x_1^p x_2]` is spanned by monomials `x_1^a x_2^b` with
  `a >= pb`.
  - A product of elementary matrices with entries in a subring has all its
    entries in that subring. So every element of `alpha_(A_1)(Gamma_0)` has
    entries in `S_1`.
  - `e_12(p x_2)` lies in `Gamma_0`, since `p x_2 in Z[x_1,x_2]` and its value at
    `1` is `0 mod p`. Its entry `p x_2` is not in `S_1`.

  For `A_2`, use `x_1 -> x_1 x_2^p`, `x_2 -> x_2` and the element `e_12(p x_1)`.
* **Free monoid.** For `p >= 2` the matrices `A_1, A_2` generate a free group, by
  ping-pong on `Z^2` with the regions `|x| > |y|` and `|x| < |y|`. So the
  positive words are pairwise distinct. In a free monoid, `u a = v b` with letters
  `a != b` is impossible. QED
