# Stable infiniteness kills every MF quotient of large elementary groups

Lane `un-paradox` (UN swarm, target U1), 2026-09-13. Part 1: the ring-level theorem.
Status: complete written proof, **unreviewed**. It extends the printed `thm:full-defect-ring` and
`cor:simple-infinite-ring` of `non_mf_groups_exist.tex` from a properly infinite unit to a properly
infinite *multiple* of the unit, meaning a ring some of whose matrix rings are not directly finite.
The analytic input is the printed theorem, unchanged.

## 0. Statement

Let `R` be a countable unital ring. In the monoid `V(R)` of isomorphism classes of finitely
generated projective right `R`-modules, with the algebraic preorder (`x <= y` iff `y = x + z`), write
`[1] = [R_R]`.

**Theorem P.** Suppose `2n[1] <= n[1]` in `V(R)` for some `n >= 1`. Then for every `N >= 2n` every
homomorphism from `EL_N(R)` to an MF group is trivial.

**Corollary P1 (simple rings).** Let `R` be a countable simple unital ring that is not stably
finite, and let `n` be least with `M_n(R)` not directly finite. Then for every `N >= 2n` every
homomorphism from `EL_N(R)` to an MF group is trivial.

- **Recovers the printed case.** `n = 1` is `full-defect-ring-non-mf-at-rank-two` (tex
  `thm:full-defect-ring`, rank-two form), by `full-idempotent-ring-has-properly-infinite-unit`.
- **Calibration, stably finite side.** If every `M_n(R)` is directly finite (for instance `R` embeds
  unitally in an algebraic ultraproduct of matrix algebras, as the Pestov 9.1 ring does), the
  hypothesis fails for every `n`. From `w_0 v_0 = 1` direct finiteness gives `v_0 w_0 = 1`, and then
  `1 = w_1 v_1 = w_1 (v_0 w_0) v_1 = (w_1 v_0)(w_0 v_1) = 0`. So Theorem P says nothing there,
  as it must: `EL_3` of the Pestov ring is LEF, hence MF.

## 1. From `V(R)` to a properly infinite unit of `M_n(R)`

**Lemma 1.** `2n[1] <= n[1]` in `V(R)` iff `S = M_n(R)` contains `v_0, v_1, w_0, w_1` with
`w_i v_j = delta_ij 1_S` for `i, j in {0,1}`. This is condition (PI) of
`full-idempotent-ring-has-properly-infinite-unit` for the ring `S`.

*Proof.* `2n[1] <= n[1]` means `R^n (+) R^n (+) Z ~= R^n` for some f.g. projective `Z`.
- Take the composite of the inclusion of the `i`-th summand `R^n` with the isomorphism: that is a
  map `v_i : R^n -> R^n`.
- Take the composite of the inverse isomorphism with the projection onto the `i`-th summand: that
  is a map `w_i : R^n -> R^n`.
- Both are elements of `End_R(R^n) = M_n(R)`, and `w_i v_j = delta_ij 1`.

Conversely, (PI) makes `(v_0, v_1) : R^n (+) R^n -> R^n` a split injection with left inverse
`(w_0, w_1)`. So `R^n (+) R^n` is a direct summand of `R^n`. QED

## 2. The block identity

**Lemma 2.** For `m >= 2` and `n >= 1`, `EL_m(M_n(R)) = EL_(mn)(R)` inside
`GL_m(M_n(R)) = GL_(mn)(R)`.

*Proof.* Index `{1..mn}` as pairs `(I, a)` with block `I in {1..m}` and `a in {1..n}`.
- (`<=`) For `I != J` and `A in M_n(R)`, the block elementary matrix `e_IJ(A)` equals
  `prod_(a,b) e_((I,a),(J,b))(A_ab)`. The factors commute, since all their off-diagonal entries lie
  in the block `(I,J)` with `I != J`, and products of such matrices have no quadratic terms.
- (`>=`) If `I != J`, then `e_((I,a),(J,b))(r) = e_IJ(r E_ab)`. If `I = J` and `a != b`, choose
  `J' != I`, which exists because `m >= 2`. The indices `(I,a), (J',a), (I,b)` are distinct, so the
  Steinberg relation `[e_ij(x), e_jk(y)] = e_ik(xy)` gives
  `e_((I,a),(I,b))(r) = [e_((I,a),(J',a))(r), e_((J',a),(I,b))(1)]`, a commutator of two elements of
  `EL_m(M_n(R))`. QED

## 3. Proof of Theorem P

1. By Lemma 1, `S = M_n(R)` satisfies (PI). By `full-idempotent-ring-has-properly-infinite-unit`
   (2 ⇒ 1), `S` has `s, t` with `ts = 1` and `S(1 - st)S = S`. `S` is countable and unital.
2. By `full-defect-ring-non-mf-at-rank-two` applied to `S`, every homomorphism from `EL_2(S)` to an
   MF group is trivial. By Lemma 2 with `m = 2`, `EL_2(S) = EL_(2n)(R)`. This settles `N = 2n`.
3. Let `N > 2n`, so `N >= 3`, and let `psi : EL_N(R) -> H` with `H` MF.
   - The embedding `A |-> diag(A, I_(N-2n))` puts `EL_(2n)(R)` inside `EL_N(R)`. The restriction of
     `psi` to this copy is a homomorphism to an MF group, so it is trivial by step 2.
   - Hence `psi(e_12(r)) = 1` for every `r in R`.
   - For `N >= 3`, signed permutation matrices in `EL_N(R)` conjugate `e_12(r)` to `e_ij(+-r)` for
     all `i != j`. So the normal closure of `{e_12(r)}` is `EL_N(R)`, as in the "All ranks"
     paragraph of the printed proof, and `psi` is trivial. QED

## 4. Proof of Corollary P1

`M_n(R)` is simple, since the two-sided ideals of `M_n(R)` are the `M_n(I)`. It is not directly
finite, so it has `ts = 1 != st`. The idempotent `e = 1 - st` is nonzero, and it is full by
simplicity. So condition 1 of `full-idempotent-ring-has-properly-infinite-unit` holds in `M_n(R)`,
hence (PI) holds there, hence `2n[1] <= n[1]` in `V(R)` by Lemma 1. Theorem P applies. QED

## 5. What this adds, and its limits

- **What is new.** The printed theorem needs a one-sided inverse in `R` itself, `n = 1`. Theorem P
  needs one only in some matrix ring, at the price of the rank threshold `N >= 2n`. In particular,
  directly finite but not stably finite simple rings fall under the no-MF-quotient mechanism once
  the rank is large.
- **Open, not claimed.** For `2 <= N < 2n` in Corollary P1 nothing is proved. The printed "passes up
  from corners" remark still gives that `EL_N(R)` is not MF whenever some corner `pRp` has a
  properly infinite unit, but triviality of every MF quotient at small rank is open.
- **Property (T).** For `N >= 3` and `R` finitely generated, `EL_N(R)` is Kazhdan
  (Ershov–Jaikin-Zapirain), so the conclusion gives finitely generated Kazhdan groups with no
  nontrivial MF quotient. Simplicity of `EL_N(R)` modulo its centre is not claimed here
  (lane un-simplicity).
- **Credit.** The analytic content is the printed one-sided Kazhdan transport and the full-defect
  theorem, together with Ershov–Jaikin-Zapirain. Lemmas 1 and 2 are standard ring theory.
