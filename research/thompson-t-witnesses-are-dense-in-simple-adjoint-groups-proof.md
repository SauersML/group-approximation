---
rg: 2
id: thompson-t-witnesses-are-dense-in-simple-adjoint-groups-proof
kind: route
title: Check (H1), (H2) and delta_1 for T over Z/4 * Z/3 and over Delta(4,3,5), then instantiate the generic Lie-closure trichotomy twice and compare the two levels
target: thompson-t-witnesses-are-dense-in-simple-adjoint-groups
requires: [lie-closure-trichotomy-without-finite-quotients, thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes, thompson-t-not-mf-iff-triangle-gap-and-rounding, thompson-t-lochak-schneps-presentation]
artifacts:
  - research/lie-closure-trichotomy-without-finite-quotients.md
  - research/lie-closure-trichotomy-without-finite-quotients-proof.md
---

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups` (the target) and
`lie-closure-trichotomy-without-finite-quotients` (the engine, cited as [GEN] with its item numbers).
All representations are finite-dimensional and unitary. Operator norms are used throughout.

## 0. The inputs, checked once per level

| input of [GEN] | level T: `Z/4 * Z/3`, `R_T = {r_1, r_2, r_P}` | level Delta: `Delta(4,3,5)`, `R_Delta = {r_1, r_2}` |
|---|---|---|
| `Gamma0` finitely generated, `R` finite | yes | yes |
| `Q = Gamma0 / <<R>>` | `T`, by `thompson-t-lochak-schneps-presentation` | `T`: `Delta / <<r_1, r_2>> = (Z/4 * Z/3) / <<r_P, r_1, r_2>>` |
| `delta_N` of [GEN] | `delta_N` of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes` | `gamma_N` of `thompson-t-not-mf-iff-triangle-gap-and-rounding` |
| (H1) `delta_N > 0` | item 1 there | item 5 there (`gamma_N` attained, positive, or `+infinity`) |
| (H2) no finite quotient of `Q` | `T` infinite simple | same |
| `delta_1` | `2 sin(pi/12) = 0.5176...`, item 1 there | `+infinity`: `Delta` is perfect |
| `eta_0 = min(1/2, delta_1)` | `1/2` | `1/2` |

**Matching the definitions of `delta_N`.**
- *Level T.* A unitary representation of `Z/4 * Z/3` of dimension `n` is exactly a pair `(A, B)` in
  `U(n)` with `A^4 = B^3 = 1`. Its [GEN]-defect over `R_T` is the `D(A, B)` of the criterion claim.
  So the two infima agree for each `n`. [GEN] takes the infimum over `dim <= N`, but the criterion
  claim's `delta_n` is nonincreasing (its item 1), so the two agree.
- *Level Delta.* A unitary representation of `Delta` is a genuine pair. Its [GEN]-defect over `R_Delta`
  is `d_T`. `gamma_n` is nonincreasing (item 5 of the rounding claim), so the infimum over `dim <= N`
  is `gamma_N`.

**`Delta` is perfect.** In `Delta^ab`, the relations `a^4 = b^3 = (ab)^5 = 1` give `a^5 b^5 = 1`, so
`a = a^5 = b^(-5) = b`. Then `a^3 = b^3 = 1` and `a^4 = 1`, so `a = 1` and `b = 1`. Hence `Delta` has no
nontrivial character, and `delta_1 = gamma_1 = +infinity`.

**(H2).** `T` is an infinite simple group (Cannon--Floyd--Parry, *Introductory notes on Richard
Thompson's groups*, Enseign. Math. 42 (1996), Theorem 5.8). A homomorphism from `T` to a finite group has
a kernel that is normal and of finite index. By simplicity the kernel is `1` or `T`, and `1` is excluded
because `T` is infinite. So it is trivial.

**Where the full presentation is used.** (H2) is a statement about `Q`, and it needs `Q = T`, which is
the imported half of `thompson-t-lochak-schneps-presentation`. At level Delta, `Q` is the same group
`T`, so the same import is used.

So both levels satisfy (H1) and (H2), with `eta_0 = 1/2`. All items of [GEN] apply verbatim.

## 1. Item 1 (level T trichotomy)

By item 3 of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, `T` is not MF iff every nontrivial
irreducible pair has `D >= eps_0` for some `eps_0 > 0`. By its item 2 this says `inf_n delta_n > 0`,
which is `gap(Z/4 * Z/3, R_T) > 0` in the notation of [GEN]. The target's `Gap_T(X)` is, word for word,
`Gap_(Gamma0,R)(X)` of [GEN] for this `(Gamma0, R)`. The [GEN] corollary gives item 1.

## 2. Item 2 (level Delta trichotomy)

(R_Delta) is `inf_n gamma_n > 0`. By Section 0 this is `gap(Delta, R_Delta) > 0`. `Gap_Delta(X)` is
`Gap_(Delta,R_Delta)(X)`. The [GEN] corollary gives item 2.

## 3. Item 3 (comparison)

Let `q : Z/4 * Z/3 ->> Delta` be the quotient map, which sends `a -> a` and `b -> b`. Let
`tau : Delta -> Inn(X(k))` be a homomorphism with dense image.
- Then `tau o q` has the same, dense, image.
- `(tau o q)(r_P) = tau((ba)^5) = 1`, and `(tau o q)(r_i) = tau(r_i)` for `i = 1, 2`.
- So `D_(R_T)(tau o q) = D_(R_Delta)(tau)`.

If `Gap_T(X)` holds with constant `eps`, then `D_(R_Delta)(tau) = D_(R_T)(tau o q) >= eps`. That is
`Gap_Delta(X)` with the same `eps`.

Chaining items 1, 3 and 2 gives: `T` not MF implies all three `Gap_T` gaps, which imply all three
`Gap_Delta` gaps, which imply (R_Delta). This is the implication "T not MF => (R_Delta)" of
`thompson-t-not-mf-iff-triangle-gap-and-rounding`, re-derived.

## 4. Item 4 (normal form)

The first two bullets are [GEN] item 5, with `eta_0 = 1/2`. For the third, take a witness sequence
`sigma_j` with `D(sigma_j) -> 0`, and fix `N`. By (H1), `delta_N > 0`. For large `j`,
`2 D(sigma_j) < delta_N`. Every ideal `h_a` of `sigma_j` has `delta_(dim h_a) <= 2 D(sigma_j) < delta_N`,
and `delta` is nonincreasing, so `dim h_a > N`. Hence `min_a dim h_a -> infinity`.

## 5. Item 5 (uniform kills)

Throughout, `eta_0 = 1/2`. A reducible representation is handled by Lemma D of the [GEN] proof: its
defect is the maximum over its irreducible summands, and at least one summand is nontrivial.

- **Finite, finite modulo scalars, virtually abelian images.** Let `K` be the closure of the image.
  - If the image is finite, `K^0 = 1`.
  - If it is finite modulo scalars, `K^0` lies in the scalars.
  - If it is virtually abelian, with abelian subgroup `A` of finite index, then the closure of `A` is
    abelian and of finite index in `K`, so it contains `K^0`.

  In all three cases `K^0` is abelian, and [GEN] item 2 gives `D >= 1/2` for every nontrivial
  irreducible. A representation of `Delta` that factors through a finite quotient `Delta ->> F` has
  finite image. Hence every nontrivial one has defect at least `1/2`, whatever `F` and whatever its
  representation.
- **Imprimitive and induced models.** This is [GEN] item 1. Its proof, in Section 1 of the [GEN] proof,
  does not use irreducibility: a summand moved by some `w_r` forces `||w_r - 1|| >= sqrt 2`. Otherwise
  the permutation action kills `R`, and Lemma T kills the action. A surface subgroup of finite index
  `m >= 2` in `Delta` gives an induced representation with `m` blocks, permuted transitively, so its
  defect is at least `sqrt 2`.
- **Fixed-group pullbacks.** This is [GEN] item 4. For `M = SO(3)`, `dim M = 3`, and the bound is
  `min(1/2, delta_3/2)` at level T and `min(1/2, gamma_3/2)` at level Delta. Both are positive by (H1),
  and `gamma_3 >= delta_3` by item 5 of the rounding claim. The bound holds for every representation
  `pi` of `SO(3)`, so it holds uniformly along `Sym^m`, `m -> infinity`. It holds for every
  homomorphism `phi : Delta -> SO(3)`, not only for the spherical-triangle one named in the target.

This proves every item of the target.

## 6. Remark: every intermediate quotient (not needed above)

Let `Z/4 * Z/3 ->> Gamma ->> T` be any finitely generated intermediate quotient, with `a, b` sent to
`a, b`, and let `R_Gamma` be the images of `r_1, r_2, r_P`.
- (H2) holds, because `Gamma / <<R_Gamma>> = T`.
- A unitary representation of `Gamma` is an exact pair with the same defect, so `delta_N^Gamma >= delta_N > 0`.
  That is (H1), and `delta_1^Gamma >= delta_1 > 1/2`.
- So [GEN] applies with `eta_0 = 1/2`, and the argument of Section 3 gives a monotone chain: if
  `Gamma ->> Gamma'`, then `Gap_Gamma(X)` implies `Gap_Gamma'(X)`.

Hence the classical gaps can only get weaker as one moves from `Z/4 * Z/3` towards `T`. At `Gamma = T`
they are vacuous, since `T` has no nontrivial finite-dimensional unitary representation. `Delta` is the
first linear stage.
