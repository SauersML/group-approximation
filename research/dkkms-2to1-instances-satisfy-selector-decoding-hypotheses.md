---
rg: 2
id: dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
kind: claim
title: The DKKMS Grassmann 2-to-1 instances meet the selector-decoding hypotheses as stated in the paper, with uniform directions tau = 2^(l-1-2k), marginal ratio K = 1 and a branch-identity defect of at most k eps, so no polynomial-time branch selector lifts an honest 3LIN encoding above one half unless NP is in RP
distinct_from:
  efficient-branch-selectors-list-decode-honest-outer-labels: that proves the decoding theorem for the abstract LEC class and leaves membership of the proved instances as an argument not checked against the paper text; this checks membership for the DKKMS 2-to-1 instances against ECCC TR16-198 Section 4.2, corrects the direction bound from 2^(l-1-3k) to 2^(l-1-2k) (the folding space H_U is excluded), handles folding, the aggregated constraints and the dirty k-tuples, and supplies the outer soundness from Lemma 5.4 of the paper.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that uses the DKKMS folding to build gauge labellings of a coarsening and kill affine-view verifiers; this uses the folding only to show that the unfolding of an honest class label is the honest restriction on clean k-tuples, and kills polynomial-time branch selectors with arbitrary views.
  dkkms-affine-view-verifiers-any-sigma-sound-at-2c-1: that is an unconditional soundness collapse for affine-view unique verifiers over DKKMS agreement games; this is a conditional completeness obstruction (NP not in RP) for orientation lifts of the DKKMS 2-to-1 game itself.
artifacts:
  - experiments/dkkms-selector-membership-2026-09-17/check_dkkms_direction_law.py
---

**ESTABLISHED.** Route: `dkkms-selector-membership-proof`.

This resolves live need `1cb0e45a` for the **2-to-1** instances of Dinur,
Khot, Kindler, Minzer and Safra, *Towards a proof of the 2-to-1 games
conjecture?* (ECCC TR16-198). These are the instances whose NP-hardness
(Theorem 1.2 of that paper, with Hypothesis 3.6 later proved by Khot, Minzer
and Safra) is the only proved 2-to-1 hardness. Membership of the KMS 2-to-2
instances is **not** treated here.

The theorem below uses neither Hypothesis 3.6 nor any inner soundness. It uses
only the construction of Section 4.2, the outer soundness Lemma 5.4, and the
hardness of regular Gap3Lin (Theorem 4.1), all quoted in the proof.

## The instance, verbatim

The paper defines the following.

* **Tuples and spaces.** `U` is the set of legitimate k-tuples `U = (e_1,...,e_k)`
  of pairwise variable-disjoint equations. `X_U` is the space of vectors
  supported on the variables of `U`, which we identify with `F_2^(3k)`.
  `H_U = Span(x_e : e in U)`, and `h_U(x_e) = b_e`, the right-hand side of `e`.
* **Vertices.** "A = {(U,L) | U∈U, L∈Gr(X_U,l), L∩H_U={0}}" and
  "B = {(V,L′) | V∈V, L′∈Gr(X_V,l−1)}".
* **Edges.** "Choose a k-tuple U ... uniformly at random and then construct a
  k-tuple V such that independently for 1 ⩽ i ⩽ k, the ith element of V is the
  equation e_i with probability 1−β and is a variable in the equation e_i with
  probability β. 2. Choose a random L′∈Gr(X_V,l−1) and a random L∈Gr(X_U,l)
  such that L′⊆L."
* **Constraint.** The constraint "accepts pairs (σ,σ′) iff σ|_{L′} = σ′".
* **Folding.** `A` is partitioned into classes `C`. Each class has a
  representative `l`-space `R` with `C = {(U,L) in A | L + H_U = R + H_U}`
  (Lemma 4.1). A class label is `σ : R -> F_2`. Its unfolding at `(U,L) in C` is
  `A(U,L) = σ~_U|_L`, where `σ~_U` is the `(H_U,h_U)`-extension of `σ`
  (Definition 4.2).
* **Folded constraints.** A constraint of `G_folded` between `C` and `(V,L′)`
  accepts `(σ,σ′)` if the unfolding of `σ` satisfies all of the `G_unfolded`
  constraints between members of `C` and `σ′`, and "The weights are summed up
  as well".

Edges are the process restricted to outputs with `(U,L) in A`, with weights
renormalized. This is the only reading under which the process defines weights
on `A x B`.

**Multi-edge form.** `G_multi` has the vertices of `G_folded`. It has one
constraint per output `((U,L),(V,L′))`, carrying its weight. That constraint
accepts `σ in Fun(R_C)` and `σ′ in Fun(L′)` iff `A(U,L)|_(L′) = σ′`.

## Statements

Fix `k`, `l`, `β` and a regular 3LIN instance `(X, Eq)`. For an assignment
`a in F_2^X`, let `ε_out(a) := Pr_(U uniform in U)[a violates some equation of U]`.
The *honest encoding* is

```text
hon(a)_C := a|_(R_C),        hon(a)_(V,L′) := a|_(L′).
```

**Outer game.** `Φ_k` has `A`-vertices `U` and `B`-vertices `V`, and `ρ` is
the law of `(U, V)` from step 1.

* `A`-labels are assignments `α in F_2^(3k)` to the variables of `U`.
* `π_UV(α) = α|_V` if `α` satisfies all equations of `U`, and `⊥` otherwise.
* The honest outer labelling is `λ^a_U = a|_U`, `λ^a_V = a|_V`.

**Annotation.** Split the `G_multi` constraint of an output `((U,L),(V,L′))`
into `2^(l-1)` equal-weight copies `e`, one for each `x in L \ L′`. Each copy
has:

* seed `w_e = (V,L′)`;
* target `a_e = U`;
* direction `x_e = x`.

An orientation `o_e` picks one preimage `o_e(σ′) in Fun(R_C)` for each `σ′`. Its
bit function evaluates the unfolding of the chosen label at the direction,
`g_e(σ′) := A_(o_e(σ′))(U,L)(x_e)`.

1. **Exact 2-to-1 and (B+).** Unfolding `Fun(R_C) -> Fun(L)` is a bijection. So
   every `G_multi` constraint is exactly 2-to-1, and the two preimages of any
   `σ′` differ at every `x in L \ L′`.
2. **Selectors on `G_folded` embed.** Take any orientation `o` of `G_folded`,
   meaning any partial bijection inside each aggregated constraint. Copy `o` to
   every multi-edge of its aggregate. This gives, in polynomial time, an
   orientation `o′` of `G_multi` with
   `val_(G_multi, o′)(h) >= val_(G_folded, o)(h)` for every labelling `h`.
3. **(E) with `τ = 2^(l-1-2k)`.** Given `(w_e, a_e) = ((V,L′), U)`, the
   direction `x_e` is uniform on `X_U \ (L′ + H_U)`. Its total variation
   distance from uniform on `F_2^(3k)` is exactly
   `2^(l-1+k) / 2^(3k) = 2^(l-1-2k)`.
4. **(M) with `K = 1`.** The law of `a_e = U` under `G_multi` is uniform on
   `U`, and so equals `ρ_A`.
5. **(B) up to the dirty mass.** Take any orientation family and any copy `e`
   whose `U` has all of its equations satisfied by `a`. If `hon(a)` satisfies
   the oriented `e`, then `g_e(hon(a)_(w_e)) = <λ^a_U, x_e>`. Hence
   ```text
   Pr_e [ g_e(hon(a)_(w_e)) = <λ^a_(a_e), x_e> ]  >=  val_(G_g)(hon(a)) - ε_out(a).
   ```
   Moreover:
   * `val_Φ(λ^a) = 1 - ε_out(a)`;
   * `val_(G_multi)(hon(a)) >= 1 - ε_out(a)`;
   * `ε_out(a) <= k ε_3 / (1 - O(k^2/|X|))` when `a` violates an `ε_3`
     fraction of `Eq`.
6. **Decoding.** Theorem 1 of
   `efficient-branch-selectors-list-decode-honest-outer-labels` holds for
   `(Φ_k, G_multi)` with this annotation, with `m = 3k` and `K = 1`. The
   witnesses are `hon(a)` with `ε_out(a) <= ε*`, and `(γ, ε)` is replaced by
   `(γ - ε*, ε*)`. So the conclusion `Lang in RP` holds whenever:
   * `τ <= (γ - ε*)/4`;
   * `s < c0/2`, where `c0 = p^2 - 2ε*` and `p = (γ - ε*)^3 2^(-l-2)`.
7. **Corollary.** Assume `NP not in RP`, and fix:
   * `γ in (0, 1/2]` and `l >= 2`;
   * the constant `q` of the outer game of Lemma 5.4;
   * an inverse-polynomial confidence `θ`.

   Put `p = (γ/2)^3 2^(-l-2)`. Take `k` so large that `2^(l-1-2k) <= γ/8` and
   the Lemma 5.4 soundness `ε_k = exp(-k/exp(ql))`, read with its implicit
   constants, is below `p^2/8`. Then take `ε_3 > 0` with
   `2kε_3 <= min(γ/2, p^2/8)`.

   For these parameters and all large inputs, no randomized polynomial-time
   selector on `G_folded` or `G_multi` has the following property: on every YES
   instance of regular `Gap3Lin(1-ε_3, s*)`, with probability `>= θ` over its
   coins, some assignment `a` satisfying a `1-ε_3` fraction of `Eq` has an
   honest encoding with orientation-lift value `>= 1/2 + γ`.

   The same conclusion covers any lift labelling that differs from such a
   `hon(a)` at endpoints of constraint mass `<= γ/4`, after choosing the
   parameters for `3γ/4` in place of `γ`.

**Correction to the scope paragraph of the parent claim.** The direction is
uniform off `L′ + H_U`, which has dimension `l-1+k`, not off an
`(l-1)`-space. So `τ = 2^(l-1-2k)`, not `2^(l-1-3k)`. There is no separate
smoothness loss, because `(E)` conditions on the seed `V`. The bound still
tends to `0` as `k` grows with `l` fixed.

## Consequences for `rich-2to1-games-conjecture`

* **Honest witnesses are dead on the proved instances, verbatim.** The
  orientation-lift route to rich 2-to-1 hardness needs an efficient branch
  selector on proved 2-to-1 instances with high lift completeness. On the
  DKKMS instances, and for every selector however global its view, the
  completeness witness cannot be the DKKMS-style honest encoding `a|_R` of a
  good 3LIN assignment, or anything within mass `γ/4` of it, unless
  `NP in RP`.
* **What did the work.** Three facts from the construction make the kill apply.
  - Folding makes the honest class label unfold to `a|_L` on every clean
    k-tuple.
  - The Grassmann edge law picks the new direction uniformly outside the
    `(l-1+k)`-space `L′ + H_U`.
  - The U-marginal is untouched by the validity conditioning.
* **Survivor (H2), sharpened.** Any orientation-lift completeness witness on the
  DKKMS instances must be far from every honest encoding of every good
  assignment. The *dirty* k-tuples do not help: they cost only
  `ε_out <= kε_3`, which the corollary absorbs. So the witness needs genuinely
  non-honest labels on a constant fraction of the clean mass, not merely
  different choices on k-tuples with violated equations.
* **Not covered.** The KMS 2-to-2 instances, and any other composition, are not
  treated. Item 6 needs only (E), (M) and the dirty-mass form of (B), so
  checking another instance means repeating Items 3-5 for it.

This neither proves nor refutes UGC or the Rich 2-to-1 Games Conjecture.

## Artifact

`check_dkkms_direction_law.py` has two parts.

**Part A** models one DKKMS block, with `X_U = F_2^(3k)` and disjoint equations,
and enumerates every valid `L ⊇ L′`. It checks four things:

* A1: the number of valid supersets;
* A2: the exact law of `x_e`, which is uniform off `L′ + H_U`;
* A3: `TV = 2^(l-1-2k)`, exactly;
* A4: `Pr[L′ ∩ H_U = 0 | V]` depends on `V` only through the number of kept
  equations.

It runs all `(V, L′)` for `(k,l) = (2,2), (2,3)` (180 and 870 cases), and
samples for `(3,2), (3,3), (4,2)`. There are 0 failures. A3 fails for the parent
claim's formula `2^(l-1-3k)` whenever `k >= 1`.

**Part B** runs all right-hand sides `b`, all assignments `a`, and all pairs
`(R, L)` avoiding `H_U` with `L + H_U = R + H_U`. That is exhaustive for `k=2,
l=2` (8960 pairs), and sampled for `k=3`. It checks:

* the unfolding bijection (Item 1);
* that the two preimages differ at every direction outside `L′` (B+);
* that on clean `U` the unfolding of `a|_R` is `a|_L`. There are 573440 such
  checks, with 0 failures.

As a control, on dirty `U` the unfolding differs from `a|_L` in 1290240 of
1720320 cases. So the dirty-mass term in Item 5 is not vacuous.
