# Covariant diagonals on the defect piece: scope, and the letterwise firewall

Lane `w4-defect-cov`, 2026-09-12. Target: `leavitt-two-root-defect-piece-forces-covariant-diagonal`, route
`el3-rank-triviality-via-defect-piece-covariance`. Builds on the adversarial audit
`research/artifacts/covariant-diagonal-plan-adversarial-audit-2026-09-12.md` (w4-r4-adversary) and on
section L9 of `research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md`.

## 0. Summary

* **Already settled elsewhere, not repeated here.** The claim is equivalent to the characteristic-two gate,
  refined root spans coincide, and sibling root groups overlap in their regular model (audit Sections 2-4,
  L9, `covariant-monotone-cylinder-families-in-rank-models-are-constant`).
* **Section 1: scope.** On the defect piece only `iota_0(V)` acts, on cylinders of `[0]`. Read literally,
  the claim is satisfied by a Dirac family on the cylinders `[1^k]`, so the route needs the index set
  restricted to cylinders of `[0]`. With that scope the audit's Corollary 3 applies.
* **Section 2 (established): the letterwise firewall.** Every multiple HNN extension of a countable locally
  finite subgroup containing the corner pair, along single-letter partial conjugations by arbitrary units,
  carries a characteristic-two rank model with two-root defect `3/8`. So measure-changing prefix
  replacements, used one letter at a time, cannot force the identity or produce the diagonal. A proof must
  use relations of `G` that fail in every such HNN extension, for instance a relation among two or more
  letters.
* **Section 3 (established): swap-group lift trees.** Torsion lifts of cylinder projections give, at every
  cylinder, a covariant exact halving `E_w = A_(w0) + A_(w1)` into conjugate orthogonal idempotents of rank
  `eps/2`. This is the rank halving between depths that the audit asks for, but the halves never are the
  next depth's pieces: `rk(A_(wi) - E_(wi)) >= eps/2`, carried by an evaluation-kernel element.
* **Section 4: where it stops.**

Notation follows the defect-piece artifact: `R = L_(F_2)(1,2)`, `G = R^x`,
`iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`, `Gamma = iota_0(G)`, corner pair
`x' = iota_1000(x_12(1))`, `y' = iota_1000(x_23(1))`, `sigma : G -> M^x` a homomorphism into the units of a
rank ultraproduct over a field of characteristic two, and `sigma~ : F_2[G] -> M` its linear extension, a
unital ring homomorphism.

## 1. Scope of the claim

* **Which symmetries act on Q.** `x'` and `y'` commute with `Gamma`, so `sigma(Gamma)` preserves `qM`
  (Theorem 1.2(1) of the defect-piece artifact). A general `v` in `V` moves the corner pair to another
  cylinder and moves `Q`. The symmetries available on `Q` are `V cap Gamma = iota_0(V)`, which fixes `[1]`
  pointwise and acts on the cylinders of `[0]`. Section 3.1 of the strategist artifact says exactly this.
  If covariance is instead required for all of `V`, as the node's wording suggests, the `e_w` cannot stay
  inside `Q`, and the audit's Corollary 3 applies directly.
* **The literal statement holds trivially.** In the corner `qMq` with the model `tau_Q(g) = q sigma(g) q`,
  put `e_(1^k) = q` for `k >= 0` (with `[1^0] = X`) and `e_w = 0` for every other cylinder.
  - Additivity: `e_(1^k 0) + e_(1^k 1) = 0 + q`, and both children of any other cylinder are `0`.
  - Covariance under `iota_0(V)`: these elements fix every `[1^k]`, `k >= 1`, and carry cylinders of `[0]`
    to cylinders of `[0]`, where `e = 0`; `tau_Q(v) q tau_Q(v)^-1 = q`.
  - Positive rank: `e_[1] = q` has rank `delta > 0`.

  So every nontrivial model satisfies the claim as written, and step 3 of the route does not follow: the
  halving obstruction needs a group acting transitively on the proper clopens of the index space.
* **Correct scope.** Index the `e_w` by cylinders of `[0]`, require covariance under `iota_0(V)`, and require
  positive rank on some cylinder inside `[0]`. Transporting by `iota_0`, this is a covariant orthogonal
  diagonal for the Cantor system `V ↷ X` in the nonzero corner, which the audit's Corollary 3 (or
  `thompson-v-cantor-system-has-no-covariant-rank-model`) excludes. So with the corrected scope the claim
  is equivalent to the characteristic-two gate, as the audit and L9 found.

## 2. The letterwise firewall

**Definition.** Let `Lambda <= G` be a countable locally finite subgroup and `I <= G` a countable set. For
`g` in `I` put `B_g = Lambda cap g^-1 Lambda g` and `phi_g(a) = g a g^-1`. The multiple HNN extension is

```text
H(Lambda, I) = < Lambda, t_g (g in I) | t_g a t_g^-1 = phi_g(a) for a in B_g > .
```

It maps to `G` by `t_g -> g`. Its relations are those of `Lambda` and the single-letter partial
conjugations; it has no relation among two or more letters.

**Theorem 2.1.** Suppose `Lambda` contains `x'` and `y'`. Then `H(Lambda, I)` has a rank model `sigma` over
`F_2` with

```text
rk( (sigma(y') - 1)(sigma(x') - 1) ) = 3/8 .
```

*Proof.*
1. **Regular tower.** Write `Lambda` as an increasing union of finite subgroups `Lambda_j`. At stage `j`
   let `lambda_j` be the left regular representation of `Lambda_j` on `F_2[Lambda_j]`, and put
   `sigma_j(a) = lambda_j(a)` once `a` lies in `Lambda_j`. Along a nonprincipal ultrafilter,
   `sigma_reg = [sigma_j]` is a homomorphism `Lambda -> M^x`, since each relation among finitely many
   elements holds exactly at all large stages. For a finite `Q <= Lambda` and `xi` in `F_2[Q]`,
   `F_2[Lambda_j]` is a free `F_2[Q]`-module, so `rk(sigma_reg(xi)) = rank(lambda_Q(xi)) / |Q|`.
2. **One letter.** Exhaust `B_g` by the finite groups `Gamma_i = B_g cap Lambda_i`. Choose `i(j) -> infinity`
   with `Gamma_(i(j))` and `phi_g(Gamma_(i(j)))` inside `Lambda_j`. Through `a -> lambda_j(a)` and through
   `a -> lambda_j(phi_g(a))`, `F_2[Lambda_j]` is a free `F_2[Gamma_(i(j))]`-module of the same rank
   `[Lambda_j : Gamma_(i(j))]`, because `phi_g(Gamma_(i(j)))` is a subgroup of the same order. So there is an
   invertible `X_j` with `X_j lambda_j(a) X_j^-1 = lambda_j(phi_g(a))` for all `a` in `Gamma_(i(j))`. Every
   `a` in `B_g` lies in `Gamma_(i(j))` for large `j`, so `[X_j]` intertwines on all of `B_g`.
3. **All letters.** Choose the intertwiners independently for the countably many letters.
4. **The defect.** `x'` and `y'` are involutions whose commutator `iota_1000(x_13(1))` is a central involution,
   so `Q_0 = <x', y'>` is dihedral of order 8. With `a = 1 + [x']`, `b = 1 + [y']`, `F_2[Q_0]` has basis
   `1, a, b, ab, ba, aba, bab, abab`, with `a^2 = b^2 = 0` and `abab = baba` spanning the socle. The right
   ideal `ba F_2[Q_0]` is spanned by `ba, bab, abab`, so left multiplication by `ba` has rank 3 on the
   8-dimensional module. By step 1 the defect has rank `3/8`. (This matches item 3 of
   `unitriangular-data-cannot-assemble-corner-leavitt-families`.) QED

The intertwiner step is the characteristic-free argument of `level-unit-hnn-extension-rank-models-proof`,
there run over the ternary level group with an anti-central twist.

**Examples of Lambda.** The corner copy `iota_1000(UT_3(R))`; products of corner copies of `UT_3(R)` over
disjoint cylinders, one of them `[1000]`; the halving group
`iota_(A0)(UT_3(R)) x iota_(A1)(UT_3(R)) ⋊ <iota_A(w)>` of `w4-r4-orth` with `A = 100`; any finite subgroup
containing `Q_0`.

**Consequence 2.2.** The two-root identity `N_23 N_12 = 0` is not a consequence of the following, together
with ring operations and ranks in `M`:
* the relations of one countable locally finite subgroup containing the corner pair;
* single-letter partial conjugations by arbitrary units of `G`, including measure-changing prefix
  replacements, compressors, Weyl elements and torus units.

A proof has to use relations of `G` that fail in `H(Lambda, I)` for every such `Lambda` and `I`. Examples:
- a relation among two or more letters: `V`'s multiplication table on depth-changing elements, commutation
  of disjointly supported letters, two letters meeting on a common domain;
- a one-letter relation that is not a partial conjugation, such as the order of a torsion letter.

This sharpens the L9 kill test ("`sigma` outside that locally finite subgroup, most likely on the prefix
replacements") to "relations beyond letterwise conjugation". The same holds for the defect-piece covariance
plan: its covariance is letterwise, so the additivity of a diagonal must come from such relations.
