---
rg: 2
id: kazhdan-sofic-models-carry-long-scale-monodromy
kind: claim
title: In a marked almost action of a finitely presented Kazhdan group without finite quotients, some trivial word of filling radius at least log(c m/eps)/log(2|S|) fails to close on a path avoiding every relator defect
distinct_from:
  kazhdan-consistent-partial-models-round-to-finite-actions: that is the global rounding theorem for consistent sets; this is its finitely presented local-to-global form, where consistency on balls follows from relator closure by a van Kampen spanning-tree argument, and the output is a lower bound on the scale of the monodromy.
  inner-realizers-are-at-least-half-the-sofic-radius: that bounds realizer length by the local sofic radius in extensions by Kazhdan kernels; this bounds the filling radius of the open trivial words of an arbitrary marked almost action.
  titz-witzel-sofic-gate-two-generators-four-approximate-relators: that is the finite gate for the kernel; this says that any solution of such a gate must route its defects through words of large filling radius.
---

**OPEN (demoted 2026-09-17 after referee audit; see Attempts).** Let `G = <S | R>` be finitely presented, with `S` finite and
symmetric and `R` finite. Let `kappa` be a Kazhdan constant for `S` in the convention (KP) of
`kazhdan-consistent-partial-models-round-to-finite-actions`, and assume `G` has no nontrivial
finite quotient. Let `sigma : S -> Sym(n)` be arbitrary. Put `c_kappa = kappa^2/(2kappa^2+2)`, and

```text
m = max_(s in S) d_H(sigma(s), 1),
delta_r = d_H(sigma(r), 1),
eps = 2 sum_(r in R) |r| delta_r.
```

Call `x` **good** if every cyclic rotation of every `r^(±1)`, `r in R`, closes at `x`, and **bad**
otherwise. For a word `w` trivial in `G`, let `rho(w)` be the least `rho` such that some van Kampen
diagram for `w` has every vertex within distance `rho` of the base vertex in its 1-skeleton.

1. **Filling lemma.** If every point of the ball `B(x, rho(w))` of the Schreier graph of `sigma` is
   good, then the path from `x` labelled `w` closes.
2. **Scale bound.** The bad points number at most `eps n`. For every integer `R_0 >= 0` with

   ```text
   2 eps (2|S|)^(R_0) < c_kappa m,                                              (LS1)
   ```

   there are a point `x` and a trivial word `w` with `rho(w) > R_0` whose path from `x` stays at
   distance `> R_0` from every bad point and does not close.

**Consequences.**

* **(C1) Monodromy scale.** A marked almost action (`m >= m_0 > 0`, `eps -> 0`) of such a group has
  open trivial words at filling radius `R_0 >= log(c_kappa m_0/(2 eps))/log(2|S|) - 1`, far from
  every relator defect. Local correctness on balls of radius `R_0`, at all but an
  `eps (2|S|)^(R_0)` fraction of points, can never supply a mark. What supplies it is monodromy
  around loops that are not filled inside any ball of radius `R_0` about a good point.
* **(C2) For the kernel.** `K = Gamma_1^2` (`titz-witzel-simple-kazhdan-cat0-lattices-exist`) is
  finitely presented, simple, infinite and Kazhdan, so the lemma applies. Every solution of the
  kernel's marked gate with relator defect `eps` has, in the complement of the
  `R_0`-neighbourhood of its bad set, an open trivial word of filling radius `> R_0`. Here `R_0`
  is of order `log(1/eps)`. Constructions that fix relators locally (Kun's expander decomposition,
  Alekseev--Drigalla deletion, radius-`r` label rigidity) cannot by themselves yield a mark. A
  sofic model of `K` must carry, at logarithmic scale, the same kind of large-loop monodromy as a
  branched or non-normal cover.
* **(C3) What would refute the kernel's soficity.** It suffices to show that for every almost
  action of `K` the open trivial words can be pushed into a set of density `o(1)`. By
  `kazhdan-consistent-partial-models-round-to-finite-actions` this collapses all generators. That
  is the deletion-repair problem of `titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair`.

**Calibration.** The ball-count factor `(2|S|)^(R_0)` is the only loss. For amenable `G` (no (T))
the conclusion fails: Folner models are consistent on sets of density `1 - O(eta)`, with no open
trivial word at any scale (Folner calibration in
`kazhdan-consistent-partial-models-round-to-finite-actions`). Whether `rho` grows linearly in
word length for `K` (as expected for a CAT(0) group) is not imported here, so the statement is
kept in terms of `rho`.

Drafted proof, now an attempt, in `kazhdan-sofic-models-carry-long-scale-monodromy-proof`.

## Attempts

### 2026-09-17: route `kazhdan-sofic-models-carry-long-scale-monodromy-proof` refuted by referee audit

Proof artifacts kept as an attempt: `research/kazhdan-sofic-models-carry-long-scale-monodromy-proof.md`
(van Kampen tree-cotree filling lemma, bad-set count, and the scale bound through CP1 of
`kazhdan-consistent-partial-models-round-to-finite-actions`). Of the referee lenses, lens 1
returned *refuted* and lens 2 returned *survives*. Both lenses found the bad-set count, the filling
lemma and the scale bound sound. The route now requires the OPEN premise
`titz-witzel-kernel-kazhdan-constant-and-no-finite-quotient`, so this claim derives OPEN.

Refutation reason (lens 1, verbatim):

> Items 1 and 2 hold up when checked step by step. The bad-set count |B| <= eps n is right: each rotation of r^(±1) is conjugate to sigma(r), so it fails at delta_r n points, and there are 2|r| rotations. The tree-cotree filling lemma is right: BFS tree of depth <= rho, non-bridge edges appear once on a face walk, faces handled in order of decreasing cotree depth, and rho is the same under either reading convention because reversing every word is an anti-automorphism taking <<R>> to <<rev R>>. The scale bound is right: a ball has at most 2(2|S|)^(R_0) points, so eta <= 2 eps (2|S|)^(R_0) < c_kappa m, and CP1 with eta/c_kappa = (2+2/kappa^2) eta gives the contradiction. CP1 in kazhdan-consistent-partial-models-round-to-finite-actions says exactly what is used: same (KP) convention, same Hamming count, same no-finite-quotient hypothesis. The first step that does not follow is (C2) and proof section 4, which apply the lemma to K = Gamma_1^2 and take finite presentation, property (T) and simplicity from the required prerequisite titz-witzel-simple-kazhdan-cat0-lattices-exist. That node says something different. There Gamma_i^q = pi_1(Y_i^q) are the lattices that are NOT residually finite, and simplicity is claimed only for their finite residuals Gamma^_i^q. It never says that Gamma_1^2 itself is simple or has no finite quotient. The route's own wording, "a finite-index subgroup of a finitely presented group", reads K as the residual, which contradicts the name it uses. K = Gamma_1^2 is simple only in the paper's other notation (Gamma = the finite residual of barGamma, Theorem 4.1: no finite-index subgroups). That appears in the artifact titz-witzel-sofic-structure-audit-2026-08-26 and the node radu-bmw-lattice-embeds-in-titz-witzel-kernel-citation, and the route requires neither. A second, smaller gap is also in (C2): nothing imported gives a positive Kazhdan constant for K in the distance form (KP); property (T) is only asserted. So the imported result does not state what (C2) uses, and the hypothesis 'no nontrivial finite quotient' for K = Gamma_1^2 is unsupported by what the route cites.
