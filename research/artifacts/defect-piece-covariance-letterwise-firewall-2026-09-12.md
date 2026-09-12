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

## 3. Swap-group lift trees

**Lemma 3.1 (identities in F_2[S_3]).** Put `u = 1 + s_0 t_1`, `v = 1 + s_1 t_0`, `c = vu`, and let
`s = S[1]T[0] + S[0]T[1]` be the swap in `V`.
* (a) `u` and `v` are involutions generating a copy of `S_3`, `c` has order 3, and `s` conjugates `u` to `v`
  and `v` to `u`.
* (b) `e = 1 + [c] + [c^2]` is a central idempotent of `F_2[S_3]`.
* (c) `p_0 = 1 + [u] + [v] + [uv]` and `p_1 = 1 + [u] + [v] + [vu]` are orthogonal idempotents with
  `p_0 + p_1 = [c] + [c^2] = 1 + e`, and `s p_0 s^-1 = p_1`.
* (d) Under the evaluation map `ev : F_2[G] -> R`: `ev(p_0) = s_0 t_0`, `ev(p_1) = s_1 t_1`, `ev(e) = 0`.

*Proof.*
* (a) `t_1 s_0 = 0` gives `u^2 = 1`, and likewise `v^2 = 1`. Through `R ≅ M_2(R)`, `r -> (t_i r s_j)`, the
  elements are `u = [[1,1],[0,1]]`, `v = [[1,0],[1,1]]`, `c = [[1,1],[1,0]]`, and `c` has order 3. From
  `s s_0 = s_1` and `t_1 s = t_0`, `s u s = 1 + s_1 t_0 = v`.
* (b) `u c u = c^-1 = c^2`, so `e` is central, and `(1 + c + c^2)^2 = 1 + c^2 + c^4 = e` in characteristic 2.
* (c) `F_2[S_3] = F_2[S_3] e x F_2[S_3](1 + e)`. On the first factor `c` acts as 1 and `u = v`, so `p_0` and
  `p_1` map to `1 + u + u + 1 = 0`. The second factor is `M_2(F_2)` through the matrices in (a), where
  `p_0 = [[1,0],[0,0]]`, `p_1 = [[0,0],[0,1]]` and `1 + e = I`. An element vanishes iff both components do.
  `s` swaps `u` and `v`, hence `uv` and `vu`.
* (d) `ev(u + v) = s_0 t_1 + s_1 t_0` and `ev(uv) = 1 + s_0 t_1 + s_1 t_0 + s_0 t_0`, so `ev(p_0) = s_0 t_0`,
  and symmetrically `ev(p_1) = s_1 t_1`. `1 + c + c^2 = 0` as a matrix identity over `F_2`. QED

This is the symmetric form of `w3-kap-visible`'s split: its `P0^ = [u] + [v] + [vu]` equals `p_0 + e`, and
`P1^ = p_1`.

**Theorem 3.2 (lift trees halve but never refine).** Let `sigma` be a nontrivial rank model of `G` over a
field of characteristic two. For a proper cylinder `w` let `c_w = iota_w(c)`, extend `iota_w` linearly to
`F_2[G]`, and put

```text
E_w = sigma~(iota_w(1 + e)) = sigma(c_w) + sigma(c_w)^2,     A_(wi) = sigma~(iota_w(p_i))  (i = 0, 1).
```

1. `E_w`, `A_(w0)`, `A_(w1)` are idempotents, `A_(w0) A_(w1) = A_(w1) A_(w0) = 0`, and `A_(w0) + A_(w1) = E_w`.
2. If `g` in `V` carries `w` onto a cylinder `gw` by prefix replacement, conjugation by `sigma(g)` carries
   `E_w`, `A_(w0)`, `A_(w1)` to `E_(gw)`, `A_((gw)0)`, `A_((gw)1)`.
3. There is `eps > 0` with `rk(E_w) = eps` for every proper `w`, and `rk(A_(w0)) = rk(A_(w1)) = eps/2`.
4. `ev(iota_w(p_i)) = 1_[wi] = ev(iota_(wi)(1 + e))`, so `A_(wi)` and `E_(wi)` lift the same cylinder
   projection. Yet `rk(A_(wi) - E_(wi)) >= eps/2`, and `A_(wi) - E_(wi) = sigma~(kappa_(w,i))` with
   `kappa_(w,i) = iota_w(p_i) + iota_(wi)(1 + e)` in the kernel of `ev`.

*Proof.*
1. `iota_w` is a group homomorphism, so its linear extension is a ring homomorphism. Compose with `sigma~`
   and apply Lemma 3.1(b), (c).
2. `g iota_w(h) g^-1 = iota_(gw)(h)` (Fact 1.2 of the descent artifact), extended linearly.
3. **Constant rank.** Any two proper cylinders are related by a prefix replacement in `V` (Lemma 2.2 of the V
   covariance artifact), so `rk(E_w)` is one number `eps`.
   * **Halves.** `sigma(iota_w(s))` conjugates `A_(w0)` to `A_(w1)` by Lemma 3.1(c), and ranks of orthogonal
     idempotents add (Lemma 2.1(b) there). So `rk(A_(wi)) = eps/2`.
   * **Positivity.** `G` is simple (`binary-leavitt-unit-group-is-simple`), so the nontrivial `sigma` is
     injective and `sigma(c_w) != 1`. If `E_w = 0`, then `sigma(c_w)^2 = sigma(c_w)`, so `sigma(c_w) = 1`.
     Hence `E_w != 0`, and faithfulness of `rk` gives `eps > 0`.
4. `ev(iota_w(h)) = S[w] h T[w] + (1 - S[w]T[w])`. `p_i` has four terms, so the complement contributes
   `4(1 - S[w]T[w]) = 0` and `ev(iota_w(p_i)) = S[w] s_i t_i T[w] = 1_[wi]`. `1 + e = [c] + [c^2]` has two
   terms and `c + c^2 = 1` in `R`, so `ev(iota_(wi)(1 + e)) = 1_[wi]`. Finally
   `rk(A_(wi) - E_(wi)) >= rk(E_(wi)) - rk(A_(wi)) = eps/2`. QED

**Remarks.**
* **Halving exists; chaining does not.** Every covariant piece `E_w` splits exactly into two conjugate halves
  of rank `eps/2`. That is the rank halving between depths asked for in Section 5 of the audit, for pieces
  built from torsion. But the covariant piece at the child is `E_(wi)`, of rank `eps`, not `A_(wi)`. The
  difference is an evaluation-kernel element of rank at least `eps/2` in every nontrivial model, so the tree
  never refines, as the audit's Corollary 3 requires. No defect is used.
* **Defect images overlap in every model.** For disjoint proper cylinders `A, B` with proper union, `D_A` and
  `D_B` commute, so `D_A M cap D_B M` contains `D_A D_B M`. On a nontrivial fixed-point-free model its rank is
  `f(2) >= c_* delta > 0` (`nested-two-root-defect-pieces-decay-geometrically-both-ways`). So defect images
  are never orthogonal in any nontrivial model, not only in the regular model of L9's kill test.
* **Firewall.** Theorem 3.2 uses only relations of the finite groups `iota_w(S_3)` and letterwise conjugation
  by prefix replacements. By Section 2, making such a tree refine needs relations beyond letterwise
  conjugation.

## 4. Where it stops

* **Status.** With the scope of Section 1, the claim is the characteristic-two gate (audit Corollary 3).
* **Every natural input is inert.**
  - Root spans are constant (audit Theorem 2).
  - Defect images overlap (Section 3, Remarks).
  - Torsion lift trees never refine (Theorem 3.2).
  - Letterwise data never force the identity (Theorem 2.1).
* **What a proof must use.** Relations of `G` beyond one locally finite subgroup and letterwise
  conjugation. Candidates:
  - products of depth-changing letters acting on the lift tree. A single letter such as `x_0`, taking `[0]`
    to `[00]`, carries `E_[0]` to `E_[00]` at constant rank and halves nothing;
  - commutation of disjointly supported depth-changing elements;
  - corner locality, where "R has no rank model" enters through all of `G`.
* **Open.** No multi-letter relation is known to force a rank loss.
