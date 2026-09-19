---
rg: 2
id: contraction-branch-capacity-forces-collision
kind: claim
title: Incoming Hilbert-Schmidt mass above a corner's capacity must appear as cross-Gram overlap
artifacts:
  - research/artifacts/pauli-overlap-dichotomy-2026-08-20.md
distinct_from:
  gram-branching-capacity-with-overlap: that is stated for partial isometries, whose source traces are the natural mass, and carries a leakage term; this is stated for arbitrary contractions with ranges already inside the corner, and its conclusion is a clean quadratic excess with no leakage.
  fractional-source-branch-pressure: that assembles per-target capacity inequalities into a rational branch matrix and runs a Perron argument; this is the single-target inequality in its contraction form.
  marked-copy-collision-forces-overlap-mass: that is the projection version, where the mass is a sum of traces; this allows arbitrary contractions and measures mass in squared Hilbert-Schmidt norm.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `Q` be a projection
with `tau(Q)=q>0`, and let `X_1,...,X_s in M` be contractions whose ranges lie
in `Q`, i.e. `X_a = Q X_a` for every `a`.  Put

```text
M_tot = sum_a ||X_a||_2^2.
```

Then

```text
sum_(a != b) ||X_b^* X_a||_2^2  >=  M_tot^2/q - M_tot.               (CBC1)
```

**Reproduction number reading.**  Define `R = M_tot/q`.  If `R <= 1` the bound
is vacuous.  If `R > 1` then the incoming mass exceeds the corner's capacity and
`(CBC1)` reads

```text
sum_(a != b) ||X_b^* X_a||_2^2  >=  M_tot (R - 1)  >  0,              (CBC2)
```

so a supercritical reproduction number forces a fixed positive amount of
ordered cross-Gram overlap.  Nothing here is asymptotic and no orthogonality is
assumed.

**Read the conclusion carefully: this is a budget, not an obstruction.**  The
overlap in `(CBC2)` is *compulsory*, and an exact model pays it just as a
microstate does.  So `R>1` by itself does not contradict anything; it converts
the question "does the packet branch?" into the strictly narrower question
"what do the relators force the compulsory overlap to do?".  This is the same
boundary drawn by `supercritical-network-needs-noncanonical-cuts`: what a
canonical computation can never produce is a supercritical configuration whose
*overlap vanishes*, and `(CBC2)` produces one whose overlap does not.
