---
rg: 2
id: stacked-models-force-lef-witnesses-into-doubling-towers
kind: claim
title: Stacking a phi-twisted LEF tower gives a sofic model of the mapping torus in which a LEF defect witness is exactly the doubling tower, with frame loss times log order at least log 2, so for LEF kernels the defect kill needs only fixed-algebra invariance
distinct_from:
  twisted-lef-tower-order-budget-kills-compression-defects: that is the group-level kill by Lagrange along the twisted layers, and it builds no representation of G; this turns the same tower into a sofic representation of G, identifies its Kazhdan cluster frame, and shows that a surviving defect generator makes every interior layer strictly double. It then reads the order budget as the mass-transport inequality with the same constant log 2.
  finite-scale-compressors-preserve-kazhdan-fixed-algebras: that proves fixed-algebra invariance under (FS) or (LOG), and exhibits an abstract doubling tower as a sharpness example; this proves that the stacked models of every LEF witness are doubling towers, with liminf lambda log|Y| >= log 2, the exact constant of that example. So the fixed-algebra level already detects every LEF witness, with no centralizer-level (W2) input.
  bounded-cluster-period-preserves-kazhdan-fixed-algebras: that supplies the cluster-frame, dominant-target and loss definitions used here, and the loss bound for arbitrary frames; this computes the loss exactly on one explicit family of frames.
  kazhdan-regular-block-periodizations-of-mapping-tori-are-finite: that builds operator-norm block models of the mapping torus from finite quotients of K and proves them genuine, hence trivial on a quotientless kernel; this builds Hamming (sofic) models from local embeddings of K, which exist for every LEF K, and whose wrap is a genuine sofic error of mass |a|/P.
  lef-mapping-torus-iff-stage-liftable-automorphism: that asks when the mapping torus itself is LEF; here only K is LEF, and the stacked model is sofic, never LEF, because of the wrap.
  compression-defect-dies-in-finite-dimensions: that kills the defect in genuine finite representations of G; the stacked model is not a representation of G, and it carries the defect as a strict refinement of the fixed algebra.
artifacts:
  - research/stacked-models-doubling-tower-proof.md
  - experiments/stacked-doubling-2026-09-17/stack_check.py
---

**ESTABLISHED.** Proof: `stacked-models-doubling-tower-proof`. It is elementary. It imports:
- the per-layer Lemma of `twisted-lef-tower-order-budget-proof` (Section 5, quoted verbatim in
  the proof);
- `kazhdan-marked-limits-eventually-uniform-expanders`, only to certify that the explicit
  partition below is a cluster frame (Cheeger constant bounded below).

## Setting

- `K` is a group, `phi ∈ Aut(K)`, `G = K ⋊_phi Z`, and `t k t^-1 = phi(k)`.
- `L = <S_L> <= K`, with `S_L` finite and symmetric, and `L` Kazhdan.
- A **tower** `T = (F, iota, P, B)` consists of a finite group `F`, a map `iota : K -> F`, an
  integer `P >= 1` and a finite set `1 ∈ B ⊂ K`, such that `iota` is a local embedding on
  `phi^(-m)(B)` for every `0 <= m < P`. This is the notion of
  `twisted-lef-tower-order-budget-kills-compression-defects`. Put `rho_m = iota o phi^(-m)`
  and `Pi_m = <rho_m(S_L)> <= F`.
- The **stacked model** of `T` is the set `Y = Z/P × F`, with the maps defined for
  `g = k t^j` (`k ∈ K`, `j ∈ Z`) by

  ```text
  sigma_T(g)(m, f) = ( m', rho_(m')(k) f ),        m' = (m + j) mod P ∈ [0, P).
  ```

- The **stacked frame** is the partition `Q(T)` of `Y` into the sets `{m} × Pi_m f`.

## Statement

1. **(Soficity.)** Take towers `T_n` with `P_n -> infinity`, increasing `B_n` and
   `union_n B_n = K`. Then `(sigma_(T_n))` is a sofic approximation of `G`:
   - for `g = k t^j` and `g' = k' t^(j')`, the maps `sigma(g) sigma(g')` and `sigma(g g')`
     agree off at most `|j|` levels, once `k, phi^j(k'), k phi^j(k') ∈ B_n`;
   - for `g != 1` the map `sigma(g)` has no fixed point, once `k ∈ B_n` and `|j| < P_n`.

   So it defines a sofic representation of `G`, with trace zero off the identity, along
   every nonprincipal ultrafilter.

2. **(Exact frame and loss.)** Let `s = k t^a ∈ Comp_G(L)`. Suppose `B` contains the set
   `B_0(s, z, S_L)` of the twisted-LEF proof (for some `z`), and the word ball of radius `r`
   of `(L, S_L)`.
   - Each `sigma_T(l)`, `l ∈ S_L`, preserves every cell of `Q(T)`. On the cell
     `{m} × Pi_m f` its generator graph is `Cay(Pi_m, rho_m(S_L))`, with no edits.
   - For `r -> infinity` these Cayley graphs have Cheeger constant bounded below by some
     `h(L, S_L) > 0`, for all but finitely many towers. So `Q(T_n)` is a cluster frame in the
     sense of `bounded-cluster-period-preserves-kazhdan-fixed-algebras`.
   - For every level `m` with `m + a ∈ [0, P)`, `sigma_T(s)` maps each cell at level `m`
     into a single cell at level `m + a`. Its size ratio is `[Pi_(m+a) : c_x(Pi_m)]`, where
     `x = rho_(m+a)(k)`, and this ratio is `1` or `>= 2`.
   - Hence the frame loss satisfies `lambda(T) <= |a| / P`, and

     ```text
     lambda(T) log |Y|  <=  |a| (log P + log |F|) / P.                (UP)
     ```

   In particular, subexponential towers (`log |F_n| = o(P_n)`) give sofic representations of
   `G` in the `(LOG)` regime of `finite-scale-compressors-preserve-kazhdan-fixed-algebras`.

3. **(A witness forces strict doubling at every interior layer.)** Suppose in addition that
   `z = k' t^b ∈ C_G(L)` and `l ∈ S_L` satisfy `[s z s^-1, l] != 1`. Let `J` be the set of
   levels `m` with `m, m + a, m + b, m + a + b ∈ [0, P)`, so `|J| >= P - 2(|a| + |b|)`.
   Then for every `m ∈ J`

   ```text
   |Pi_(m+a)|  >=  2 |Pi_m| ,
   ```

   and `sigma_T(s)` maps each cell at level `m` into a cell at least twice as large. This is
   the doubling-tower shape of item 4 of `finite-scale-compressors-preserve-kazhdan-fixed-algebras`,
   realized inside a sofic representation of `G` itself.

4. **(The order budget is the mass-transport inequality, with constant log 2.)** In the
   situation of item 3, for every `D > 0`,

   ```text
   lambda(T) log |F|  >=  (1 - e^(-D)) ( |J| log 2 - |a| D ) / P.        (LOW)
   ```

   Taking `D = log P` gives `lambda(T) log |Y| >= log 2 - O((|a| + |b|) log P / P)`. So along
   any sequence of stacked models with `B_n ⊇ B_0`,

   ```text
   liminf  lambda_n log |Y_n|  >=  log 2 ,
   ```

   and `(LOG)` fails with exactly the constant of the doubling tower. Summing only the
   conservation identity also gives `P <= |a| log_2 |F| + 2(|a| + |b|)`. This is the budget
   (OB4) of `twisted-lef-tower-order-budget-kills-compression-defects`, up to additive
   constants.

5. **(W1 is forced: the fixed algebra detects the witness.)** In the situation of item 3,
   there is a `±1`-valued `g ∈ D(Q(T))` whose conjugate `sigma_T(s) g sigma_T(s)^-1` has
   normalized `ℓ^1`-distance at least `|J| / (2P)` from `D(Q(T))`. Hence, along any sequence
   as in item 1 with `B_n ⊇ B_0`, `Ad sigma(s)` does not preserve `prod_U D(Q(T_n))`, the
   Kazhdan fixed algebra of `sigma(L)`. The same holds for the pair `L <= <L, s>`.

## Consequence for (EK1): the LEF branch needs only the fixed-algebra level

Contrapositive of items 1, 3 and 5. Let `K` be LEF, `L <= K` Kazhdan, and `s = k t^a` a
compressor. Suppose that in every stacked sofic representation of `G` (item 1),
`sigma(s)` normalizes the fixed algebra `prod_U D(Q(T_n))` of `sigma(L)`. Then
`[s z s^-1, l] = 1` for every `z ∈ C_G(L)` and `l ∈ L`.

Hence a LEF witness for `torsion-free-sofic-extrinsic-kazhdan-defect-kernel` is killed by
fixed-algebra invariance (Kun--Thom Proposition 3.1 level) on stacked models alone. No
centralizer normalization (Theorem 4.1 level, `(KT*)`, branch W2) is needed.

This sharpens the (W1)/(W2) split of that node's Attempt 21:
- In stacked models of a LEF kernel, W2 never occurs for a defect generator. Every LEF witness
  sits in W1, with `lambda log |Y| >= log 2`.
- The programme "show that no sofic representation of a mapping torus of a Kazhdan
  quotientless `K` carries a doubling tower", restricted to stacked models, implies the LEF
  case of the kill. By item 4 it is exactly as strong as the twisted order budget `(SUB)`.
  It is not a weaker independent prerequisite.

## Scope

- The kernel must be LEF, so that towers exist. For a merely sofic `K`, stacking an
  `epsilon`-good sofic approximation of `K` on `union_(m<P) phi^(-m)(B)` still gives a sofic
  model of `G`, with loss `<= |a|/P + O(epsilon)`. But the Lagrange dichotomy of item 2 has
  no analogue there, so W2 is not excluded. That case is not claimed.
- No property (T) of `L` is used in items 1, 3, 4 and 5. It enters only in item 2, to make
  `Q(T)` a cluster frame, so that `lambda` is the loss of the finite-scale theorem.
