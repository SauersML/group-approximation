---
rg: 2
id: thompson-t-padded-cover-stability-is-inert
kind: claim
title: "Padded stability of a cover of T's presentation is inert for the MF question: when the auxiliary block theta is nontrivial, whether the corrected representation witnesses a small T-relator defect is decided by theta alone, so only trivially padded rounding can bear on T"
distinct_from:
  torus-knot-groups-are-rq-stable: that establishes R_q-padded stability of K(3,4); this shows that such a statement, for K(3,4), Delta(4,3,5) or any cover of the Lochak--Schneps presentation, carries no information about T's near pairs beyond its trivially padded part.
  simple-kazhdan-mf-lives-in-gap-near-representations: that notes that padding by identity blocks does nothing in operator norm for the group itself; this is the corresponding statement for padding by nontrivial honest representations of a residually finite cover, which is the form in which Willett's theorems come.
  thompson-t-not-mf-iff-triangle-gap-and-rounding: that is the decomposition into (R_Delta) and (S_T); this kills the class of approaches that would supply (S_T) from a nontrivially padded stability theorem.
  dadarlat-matricial-stability-obstruction: that is a K-theoretic obstruction to stability; the death step here is not K-theoretic, it is the max-over-summands behaviour of the operator norm.
---

**ESTABLISHED** by `thompson-t-padded-cover-stability-is-inert-proof` (written proof).

## Setting

The notation is that of `thompson-t-not-mf-iff-triangle-gap-and-rounding`. Let `Gamma` be any group generated
by the images of `a, b` through which `Z/4 * Z/3 ->> Gamma ->> T` factors, for example `K(3,4)`,
`Delta(4,3,5)` or `Z/4 * Z/3`. Let `L` be the maximal length of `r_1`, `r_2` and `r_P`. For an exact pair `x`
let `D(x)` be its defect on `r_1`, `r_2` and `r_P`.

A **padded correction** of an exact pair `phi` is a triple `(theta, pi, eps)` with
- `theta` an exact pair (an auxiliary block),
- `pi` an exact pair that is a genuine `Gamma`-representation, and
- `||pi(s) - (phi (+) theta)(s)|| < eps` for `s = a, b`.

This is Willett's Definition 1.6 (arXiv:2408.13350): "there exists a map θ: Γ→M_k(C) in Q(S,ε) and a
representation π: Γ→M_{n+k}(C) in R such that ||(φ(s)⊕θ(s))−π(s)||<ε for all s∈S". The only change is that
`theta` is spectrally rounded to an exact pair, at cost `O(eps)`.

## Statement

**(Invariant.)** For every padded correction,

```text
| D(pi) - max(D(phi), D(theta)) | <= L eps.
```

**(Dichotomy.)** Let `phi` be a delta-pair and let `(theta, pi, eps)` be a padded correction of it.
- **(i) Trivial padding.** If `theta = 1_k`, then `D(pi) < delta + L eps`. This is exactly the conclusion
  that (S_T) needs.
- **(ii) Nontrivial padding.** If `theta` is nontrivial, then `pi` is nontrivial automatically, and
  `D(pi)` lies in `[D(theta) - L eps, D(theta) + delta + L eps]`.

  So whether `pi` witnesses a small `T`-defect, i.e. `D(pi) < c`, is decided by `theta` alone, up to
  `delta + L eps`. When it does, `theta` is itself a nontrivial `(c + L eps)`-pair, a witness of the same
  quality as the one being ruled out.

## The class killed

**Approaches.** Prove that `T` is not MF, or (S_T), by the following steps.
1. Start from a nontrivial small pair `phi`.
2. Apply a padded stability theorem for a cover `Gamma` of `T`'s presentation, such as `R`- or
   `R_q`-stability in Willett's sense, including `torus-knot-groups-are-rq-stable` for `K(3,4)`.
3. Obtain an honest representation `pi` of `Gamma`.
4. Derive a contradiction from a property of honest representations, such as (R_Delta).

**Invariant.** The operator-norm defect of a direct sum is the maximum over its summands, and it is
`L`-Lipschitz under perturbation of the generators.

**Death step.** This is the auxiliary block `theta`.
- If `theta` is nontrivial, the contradiction, if any, is already present in `theta` and does not involve
  `phi`.
- If `theta` is trivial, the input is (S_T) itself.
- With the uncontrolled `theta` that Willett's theorems provide, the argument proves nothing about `phi`.

Remark 1.13 of Willett says: "Theorem 1.10 gives no control on the size of the auxiliary representation θ
appearing in Definition 1.6". His Section 1.7 says: "Our methods require that Γ has a separating family of
honest representations, and so are not useful for results along these lines." `T` has no such family.

**What survives.** Only a *trivially* padded rounding onto a cover with many honest representations
survives. This is (S_T), and in T-free form (S_Delta), recorded in
`thompson-t-near-pairs-round-to-triangle-reps`. For `R_q`-padding, `pi` factors through a finite quotient
`Q` of `Gamma`. No nontrivial such `Q` is a quotient of the infinite simple group `T`, and the
dichotomy applies verbatim.

All statements assume `eps < 1`.
