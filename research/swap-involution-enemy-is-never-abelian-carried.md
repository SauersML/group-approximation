---
rg: 2
id: swap-involution-enemy-is-never-abelian-carried
kind: claim
title: A balanced free central involution maximally anticommutes with its twist, so no abelian carrier can feed the swap route
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that exhibits an abelian-carried leak (a Bernoulli coordinate unitary) whose Connes embeddability refutes the full commutant collapse; this proves that every such abelian-carried leak has commutator zero with its own twist and therefore can NEVER satisfy the amalgamated-freeness moment pattern of the double-swap enemy, so the swap route is immune to the construction that threatens the collapse routes.
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that makes the homogeneous-quotient crossed product a refutation gate for the collapse, the K-orbit cells being the leak; this shows those cells, and any signed combination of them, live in an abelian algebra invariant under the h-twist and hence fail the four-letter free moment by the maximal possible margin.
  hecke-far-commutator-defect-formula: that computes the FAR double-coset limit of the commutator defect of a subgroup-central unitary in every finite tracial algebra; this is an exact identity at ONE finite word (the four-letter alternating word at h itself), separating the free pattern from every commuting pattern with no limit taken.
  sl3-outliers-carry-no-balanced-free-involution: that is the open exclusion of the enemy on lattice outliers; this is an established structural constraint on any candidate enemy -- maximal anticommutation with its twist -- which rules out entire construction templates without deciding the open claim.
---

**THEOREM (established here; proof in
`swap-involution-abelian-carrier-proof`).**  Let `C <= A` be any pair, `M`
a tracial von Neumann algebra, `pi : A -> U(M)` trace-preserving for the
regular character, `B = W*(pi(C))`, and let `s in M` be a self-adjoint
unitary with `E_B(s) = 0` that is free from `W*(pi(A))` with amalgamation
over `B` (the double-swap enemy pattern `(IL1)` of
`hnn-stable-letter-rounds-to-finite-order`).  Then for EVERY `a in A - C`,
writing `s_a = pi(a) s pi(a)^*`:

```text
tau((s s_a)^2) = 0,   hence   || [s, s_a] ||_2^2 = 2.        (AC1)
```

That is: `s` and each of its `A`-twists generate the infinite dihedral
group freely in trace, and in particular they maximally fail to commute
-- the commutator has the largest Hilbert--Schmidt norm a commutator of
two involutions can have.

**COROLLARY (the separation of routes).**  In any crossed product
`L^infinity(X) rtimes A` (pmp action), any candidate `s` lying in the
abelian core -- a Bernoulli coordinate sign, a signed combination of
`K`-orbit cells of the homogeneous quotient, any function of `X` --
commutes exactly with all its twists (`[s, s_a] = 0`), so `(AC1)` fails
by the maximal margin: `tau((s s_a)^2) = 1`, not `0`.  Hence:

- Connes embeddability of the coset-Bernoulli wreath or of the
  homogeneous-quotient crossed product would refute the relative
  commutant collapse `(RCC)` (as the graph records) but supplies NO
  enemy for the double-swap route: the leaks those models produce are
  abelian-carried, and the four-letter moment convicts them.
- Any refutation of `sl3-outliers-carry-no-balanced-free-involution`
  must construct outlier microstates with a genuinely noncommutative
  twist structure: `s_n` and `pi_n(h) s_n pi_n(h)^*` asymptotically free
  involutions.  No dynamical model over an abelian carrier, and no
  construction in which the involution and its twist land in a common
  commutative (or, by the same computation, common finite-dimensional
  center-heavy) corner, can do it.

The collapse `(RCC)`, the projective transfer, and the amalgam-freeness
minimal forms were already known to be strictly ordered
(`hnn-hyperlinearity-is-amalgamated-free-haar-unitary`); `(AC1)` gives
the first construction-level separation: the known enemy factories all
live on the wrong side of it.

## Attempts

- **Can a noncommutative carrier be extracted from the homogeneous
  quotient anyway?**  The only candidates in `M_p` beyond the abelian
  core are the group side and mixed elements; the group side of the
  lattice is exactly what the microstates approximate, and a mixed
  `s = sum f_g u_g` with `E_B(s) = 0` needs its `u_g`-coefficients
  supported off `C` while commuting with `pi(C)` -- for the profinite
  homogeneous action the `C`-conjugation orbits on `Gamma - C` are
  infinite, forcing such coefficients to vanish in the ultraproduct
  (the same infinite-orbit argument as the wreath's ergodicity
  computation).  So the homogeneous quotient offers no second carrier;
  a genuine enemy needs a new mechanism, not a new function on `X`.
