---
rg: 2
id: sharp-two-t-actor-gives-fp-host
kind: claim
title: A finitely presented sharp-two property-T actor gives the required aperiodic two-point lamp host
distinct_from:
  simple-t-augmentation-module-is-aperiodic: that treats the regular augmentation module and encounters the ordinary wreath-product presentation obstruction; this uses a two-transitive permutation module with only two pair orbits.
  augmentation-actor-semidir-is-not-fp: that proves the regular action has infinitely many pair-difference orbits and is not finitely presented; sharp two-transitivity removes exactly that obstruction.
---

Assume that `A` is an infinite finitely presented simple property-`(T)`
group with a sharply two-transitive action on a countable set `X`, and assume
the point stabilizer `A_x` is finitely generated.  Put

```text
L=F_2^(X),             m_0=delta_x+delta_y  (x!=y).       (S2A1)
```

Then:

1. the orbit of `m_0` spans the augmentation submodule of `L`;
2. every character `chi in L^` with `chi(m_0)=-1` has infinite `A`-orbit,
   and those orbits have one uniform Schreier `ell^2` gap;
3. `L semidirect A` is finitely presented; and
4. adjoining the central D8 seed

   ```text
   z^2=J^2=1,       J central,       [m_0,z]=J             (S2A2)
   ```

   gives a finitely presented group in which `J!=1` but every exact
   finite-dimensional unitary representation kills `J`.

Sharp two-transitivity is transitivity on ordered distinct pairs, so all
pair differences `delta_u+delta_v` lie in the orbit of `m_0`; these span
the augmentation submodule, proving clause 1.  A finite character orbit is
fixed because simplicity forbids proper finite-index subgroups.  A character
of `L` is a binary coloring of `X`, and transitivity says that an invariant
coloring is constant.  Both constant colorings evaluate trivially on the
two-point seed `m_0`.  Hence every seed-visible character has infinite orbit,
and property `(T)` gives the uniform gap.

For finite presentation, the generalized permutational-wreath criterion
applies to

```text
W=C_2^(X) semidirect A = L semidirect A.                    (S2A3)
```

The actor and lamp are finitely presented, the point stabilizer is finitely
generated, and the diagonal action on `X^2` has exactly two orbits.  Hence
`W` is finitely presented.  Adding the finitely many relations `(S2A2)`
preserves finite presentation.  Using the two-point seed rather than a
single point is load-bearing: the all-ones fixed character is visible to a
single point lamp but is trivial on `m_0`.

Finally apply `infinite-character-actor-kills-fd-mark` to obtain exact
finite-dimensional invisibility.  Its `L^2(L^)` character-translation model
keeps `J=-I`, so the mark is algebraically nontrivial.

This closes the **exact groupification and finite-presentation** half of the
infinite actor route under two concrete actor hypotheses.  It does not close
normalized-HS soundness: a microstate must still be rounded to one finite
joint `L`-spectral PVM with actor covariance energy controlled by the fixed
presentation defect.  That same-basis theorem is the remaining analytic
gate.
