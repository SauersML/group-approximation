---
rg: 2
id: lin-code-space-pauli-test-has-only-logarithmic-weyl-rank
kind: claim
title: Lin's literal Justesen code-space Pauli test has only logarithmic Weyl rank
distinct_from:
  lin-gap-wrappers-retain-oracular-atlas-holonomy: that audits the projection atlas after Lin's gap wrappers assuming the Pauli rigidity input; this finds an earlier rank defect in the literal Pauli-basis sampler in arXiv:2510.07162v1.
  clifford-hs-defect-becomes-adversarial-site-noise: that asks to localize coherent error after a growing Pauli packet has been exposed; this proves that the stated code-space test does not expose the growing packet at all.
  dimension-reported-pauli-test-halting-compiler: that assumes a uniformly sound Pauli test can be activated by group words; this separates the correct generator-column test from the code-space distribution written in Lin's source.
---

Let `C <= F_2^n` have dimension `k<n`, and define the Pauli-basis test by
sampling every coordinate word `u_X,u_Z` from `C`, exactly as in Figure 6 of
Lin, arXiv:2510.07162v1.  Then the test has a perfect synchronous
oracularizable strategy using at most

```text
r+1 <= k+1                                                   (LCW1)
```

EPR pairs, where `r` is the rank of the ambient dot product restricted to
the two copies of `C`.  In particular, the literal choice in Section 7.2,
where `C` is a Justesen code of length `n` and dimension
`k=floor(log n)`, cannot rigidly certify `n` EPR pairs.

Write `G:F_2^k -> C` for a generator map and

```text
M=G^T G,             a^T M b=(Ga).(Gb),             r=rank M.
```

Factor `M=L R` through `F_2^r`, and put

```text
X_C(Ga)=X(L^T a),             Z_C(Gb)=Z(R b)          (LCW2)
```

on `r` qubits.  These are additive representations and obey the exact Weyl
law

```text
X_C(u) Z_C(v)=(-1)^(u.v) Z_C(v) X_C(u).               (LCW3)
```

Their joint spectral PVMs can be labelled by strings in `F_2^n`: every
character of `C` extends to `F_2^n`, so choose a section of
`F_2^n -> C^*`, label the nonzero atoms by that section, and set all unused
outcome projections to zero.  Coarse-graining the resulting `n`-bit output
along any queried `u in C` gives exactly `X_C(u)` or `Z_C(u)`.  Commuting
pairs have their joint PVMs, and an anticommuting pair has the usual magic-
square completion after one auxiliary EPR pair.  This supplies every PVM in
Figure 6 and wins every listed check with probability one, proving `(LCW1)`.

There is also an exact coherent kernel.  For every `v in C^perp` and every
real `theta`,

```text
U_(v,theta)=exp(i theta Z(v))
```

commutes with every tested `X(u)`, `u in C`, and with the entire `Z` chart.
Conjugating the full `X`-outcome PVM by `U_(v,theta)` therefore changes the
fine measurement while leaving every Figure-6 predicate unchanged.  Since
`dim C=k`, there is a `v in C^perp` of weight at least `(n-k)/2`: for uniform
`v in C^perp`, all but at most `k` coordinates are balanced.  Thus the
literal test admits zero-defect coherent changes supported on a linear
number of the named coordinates.  They may be absorbed by a new global
isometry, but they cannot be interpreted as a sparse bad-site set relative
to a pre-existing tape frame.

The spectral-gap assertion fails for the same elementary reason.  Uniform
measure on the proper subspace `C` does not have generating support in
`F_2^n`; every nontrivial character in `C^perp` has Markov eigenvalue one.
In de la Salle, arXiv:2204.07084v2, Example 1.2 uses the **columns of a
generator matrix** of a code of dimension `n`, viewed as a spanning subset
of `F_2^n`, not the code space of a dimension-`log n` code.  The intended
test can therefore be repaired: take an explicit asymptotically good
`[K,n,d]` code with `K=Theta(n)`, and sample its `K` generator columns using
`O(log n)` random bits.  That corrected distribution can invoke de la
Salle/Lin global Pauli rigidity.

What the correction supplies is a dimension-independent **global tensor
exactification up to an arbitrary isometry**.  It does not by itself supply
the stronger conclusion requested by
`clifford-hs-defect-becomes-adversarial-site-noise`: a sparse site-error set
in the already named tape frame.  Any use in an HS-PCP/Boone compiler must
first make the corrected generator-column questions into ordinary group
words and pin the extracted global isometry to the computation incidence.

