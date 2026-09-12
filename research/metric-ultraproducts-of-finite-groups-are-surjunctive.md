---
rg: 2
id: metric-ultraproducts-of-finite-groups-are-surjunctive
kind: claim
title: Metric ultraproducts of finite groups with invariant lengths are surjunctive
distinct_from:
  weakly-sofic-groups-are-surjunctive: that concerns countable weakly sofic groups; this is the same content for the ambient metric ultraproducts, where the rectangle-clause form of surjunctivity becomes a metric stability statement about finite groups.
  sofic-groups-are-surjunctive: that is the Hamming special case, whose counting proof consumes finite actions; this allows arbitrary invariant lengths, where no finite action is available by hamming-transports-of-weak-sofic-models-are-soficity.
refuted_by:
  - kun-thom-clifford-cover-nonsurjunctive
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

**OPEN.** Let `(H_i, l_i)` be finite groups with conjugation-invariant lengths,
`omega` a nonprincipal ultrafilter, and

```text
Q = prod_i H_i / N_omega,     N_omega = { (h_i) : lim_omega l_i(h_i) = 0 } .
```

Then `Q` is surjunctive: every injective cellular automaton on every
finite-alphabet full shift over `Q` is surjective.

**Equivalent forms.**
- `weakly-sofic-groups-are-surjunctive`: the two routes into and out of this
  claim form an intended equivalence cycle.
- Metric stability of rectangle clauses. For every rectangle clause of
  `surjunctivity-is-axiomatized-by-rectangle-clauses` and every `c > 0` there is
  `eps > 0` such that, in every finite group with an invariant length, tuples
  satisfying the forward equations up to length `eps` satisfy some reverse
  equation up to length `c`. Surjunctivity is equivalent to the clauses; a clause
  fails in `Q` exactly when forward lengths tend to `0` along `omega` while every
  reverse length stays above some `c`.
- `Q` is the abstract ultraproduct `U = prod_omega H_i` modulo its normal
  subgroup of infinitesimal elements. `U` satisfies every rectangle clause by
  Łoś's theorem, since the clauses are universal sentences true in finite groups.
  So the claim is quotient closure of surjunctivity for this one kind of kernel.

## Attempts

- **Counting on finite actions: dead.** By
  `hamming-transports-of-weak-sofic-models-are-soficity`, finite actions of the
  factors with small defects and fixed separation for every finite set exist only
  for sofic subgroups. So Gromov--Weiss charts cannot be the mechanism.
- **Normal-subgroup lengths: fine, and uninformative.** If `l_i` is `eps_i` on a
  normal `N_i` and `1` off it, with `eps_i -> 0`, then `Q` is the abstract
  ultraproduct of the finite groups `H_i/N_i`. That satisfies every rectangle
  clause by Łoś's theorem, so it is surjunctive. All the content sits in lengths
  whose small balls generate everything, such as simple factors ([WS] Theorem B).
- **Lifting to U: not enough.** A strict automaton over `Q` lifts to one over `U`
  acting on `N_omega`-invariant configurations. Injectivity off those
  configurations is not inherited, so surjunctivity of `U` gives nothing without
  an approximate-invariance argument along `omega`.
- **Open next step.** A metric counting principle: for a strict clause, bound how
  many near-solutions the forward table can have in `(H, l)` against how many
  distinct reverse-hinge words they carry. It must use the length itself, not a
  finite action.
- **Bounded-width closure form** (w4-metric-ultra, artifact
  `metric-ultraproduct-bounded-width-closure-2026-09-12.md`).
  - *The equivalence.* This claim is equivalent to
    `strict-reverse-words-lie-in-bounded-width-profinite-closures`: for every strict datum, some reverse word lies
    in the profinite closure of the products of at most `n` conjugates of forward relators.
  - *Which lengths matter.* Only Glebsky's capped conjugation word lengths are needed.
  - *The reflection kernel.* The union of those closures is the kernel of the largest weakly sofic quotient
    (`weak-sofic-reflection-kernel-is-bounded-width-closure`).
  - *The ladder.* So this claim is one rung of `N ⊆ N_ws ⊆ N_lin ⊆ N_sof ⊆ N_lef ⊆ cl(N)`
    (`surjunctivity-of-a-local-class-is-reflection-kernel-membership`). Gottschalk's conjecture is the bottom rung,
    and Gromov–Weiss supplies the fourth.
- **The metric counting principle, made exact.** The open next step above is exactly a uniform width bound: one
  reverse word that, in every finite quotient of the free group, is a product of at most `n` conjugates of forward
  relators. Finite surjunctivity puts a reverse word in each normal closure, with no bound.
- **Rank calibration** (artifact Section 3.2).
  - *Its limit.* The rank-ultraproduct proof consumes a Sylvester rank that is small on the defects. Lengths
    dominated by representation ranks give linear soficity, so the method reaches the `N_lin` rung and no further.
  - *Consequences of this claim.* It implies `linear-sofic-groups-are-surjunctive`
    (`linear-sofic-surjunctivity-from-weak-sofic-case`), and also its linear shadow
    `weakly-sofic-group-algebras-are-stably-finite`.
- **Test hosts** (artifact Section 3.3).
  - *The Clifford cover.* `E_S` is weakly sofic, so `kun-thom-clifford-cover-nonsurjunctive` refutes this claim.
  - *Leavitt units.* Together with `leavitt-unit-group-nonsurjunctive`, this claim would make `R^x` not weakly
    sofic.
