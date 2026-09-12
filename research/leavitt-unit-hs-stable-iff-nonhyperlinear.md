---
rg: 2
id: leavitt-unit-hs-stable-iff-nonhyperlinear
kind: claim
title: The binary Leavitt unit group is normalized-HS stable exactly when it is nonhyperlinear
distinct_from:
  steinberg-hs-stability-equals-nonhyperlinearity: that is the equivalence for the Steinberg cover St_5(L) and its quotient EL_4(L), with a caution that nonhyperlinearity of the cover and of the quotient differ; this identifies both groups with L^x through Khanh's comparison theorem, so the caution is vacuous, and proves the equivalence for L^x itself.
  leavitt-steinberg-hs-stable: that is the open stability claim; this is the proved equivalence that makes it literally the statement that L^x is nonhyperlinear.
  binary-leavitt-unit-group-hyperlinear: that is the open yes/no question; this proves that its negative answer is exactly normalized-HS stability of the same group and its positive answer exactly instability.
  pointwise-hs-stability-from-no-hyperlinear-quotient: that is a one-way implication for arbitrary groups in the pointwise sense; this is a two-way equivalence in the strict finitely presented sense for one simple minimally almost periodic group.
  leavitt-unit-hyperlinear-iff-projective-hs-model: that relaxes the hyperlinearity witness to projective models through the vanishing Schur multiplier; this equates the absence of any witness with normalized-HS stability, using finite presentation and minimal almost periodicity instead.
---

**ESTABLISHED.** Let `L = L_(F_2)(1,2)` and `Q = L^x`. The following are
equivalent.

1. `Q` is normalized Hilbert--Schmidt stable, in the strict same-dimension
   sense, for one and hence every finite presentation.
2. Every homomorphism from `Q` into the unitary group of a tracial matrix
   ultraproduct `prod_omega (M_(d_n), tr_(d_n))` is trivial.
3. `Q` is not hyperlinear.

Moreover

```text
St_5(L) = GL_5(L) = Q = GL_4(L) = EL_4(L)        (isomorphisms of groups)
```

So conditions 1--3 of `steinberg-hs-stability-equals-nonhyperlinearity` are
statements about the single group `Q`. The central kernel on the unstable
branch of `leavitt-steinberg-hs-stability-fork` is trivial, and
`leavitt-steinberg-hs-stable` is condition 1 above.

## Proof

Inputs:
* `Q` is finitely presented (`leavitt-unit-group-finitely-presented`);
* `Q` is simple (`binary-leavitt-unit-group-is-simple`);
* `Q` is minimally almost periodic
  (`binary-leavitt-unit-group-is-minimally-almost-periodic`): every
  homomorphism `Q -> U(d)` is trivial.

Fix a finite presentation `<S | R>` of `Q`.

* **2 <=> 3.** A nontrivial homomorphism into a tracial matrix ultraproduct
  has trivial kernel because `Q` is simple, so it witnesses hyperlinearity.
  Conversely, a hyperlinear approximation of `Q` is an injective such
  homomorphism.
* **1 => 2.** Let `pi : Q -> prod_omega U(d_n)` be a homomorphism, and lift
  each `pi(s)`, `s in S`, to unitaries `phi_n(s)`. Every relator in `R` has
  defect tending to `0` along `omega`. Stability gives, for every
  `epsilon > 0`, some `delta > 0` such that `delta`-almost representations are
  `epsilon`-close to representations. Along `omega` the defects are
  eventually below every `delta`. So there are representations
  `rho_n : Q -> U(d_n)` with `max_s ||phi_n(s) - rho_n(s)||_2 -> 0` along
  `omega`. Each `rho_n` is trivial, so `pi(s) = 1` for every generator.
* **2 => 1.** Suppose `Q` is not stable. Then there are `epsilon > 0` and maps
  `phi_n : S -> U(d_n)` whose relator defects tend to `0`, each at distance at
  least `epsilon` from every representation. Representations are trivial, so
  `max_s ||phi_n(s) - 1||_2 >= epsilon`. Along a free ultrafilter the finitely
  many vanishing relator defects make `phi` a homomorphism
  `Q -> prod_omega U(d_n)`, and it is nontrivial on some generator. This
  contradicts 2.
* **Identifications.**
  * `leavitt-steinberg-map-iso-from-rank-three` (Khanh, Theorem 5.4) gives
    `St_5(L) = GL_5(L)`.
  * `leavitt-gl-equals-el-and-perfect-unit-group` gives `GL_4(L) = EL_4(L)`.
  * A complete binary prefix code `w_1, ..., w_k` satisfies `w_i* w_j = delta_ij`
    and `sum_i w_i w_i* = 1`. So the matrix units `w_i w_j*` give a ring
    isomorphism `M_k(L) = L` for every `k >= 1`, hence `GL_k(L) = Q`.

## Consequences

* A proof of `leavitt-steinberg-hs-stable` is exactly a proof that `Q` is the
  first known nonhyperlinear group. An unstable almost-representation sequence
  of `Q` is exactly a hyperlinear approximation of `Q`.
* This is the stable-branch counterpart of the deliberate route cycle
  `leavitt-unit-hyperlinear-from-steinberg-instability` /
  `steinberg-instability-from-leavitt-unit-hyperlinear`, which identifies the
  unstable branch with `binary-leavitt-unit-group-hyperlinear`. Here the
  identification is a single established claim with a direct proof, with no
  appeal to the Steinberg fork.
* The equivalence uses neither property (T) nor the character classification
  `binary-leavitt-full-character-simplex`. Those enter only when attacking
  either side.
* This decides neither side.

DERIVATION
leavitt-unit-hs-stable-iff-nonhyperlinear-proof
