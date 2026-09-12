---
rg: 2
id: z-haar-algebraic-spectrum-proof
kind: route
title: Decompose the dual automorphism into finite cycles and bilateral shifts
target: z-haar-algebraic-factors-have-lebesgue-plus-torsion-spectrum
requires: []
---

Put `A=K-hat`.  Fourier transform identifies `L^2(K)` with `ell^2(A)` and
the Koopman unitary with the permutation induced by the dual automorphism
`alpha` of `A`.  Decompose the countable set `A` into `alpha`-orbits.

On a finite orbit of length `n` the unitary is the cyclic `n`-shift, so its
spectral measure is supported on the `n`-th roots of unity.  On an infinite
orbit, choosing one base point identifies the orbit with `Z` and the unitary
with the bilateral shift on `ell^2(Z)`, whose maximal spectral type is Haar
measure `m_T` on the circle.  Hence a maximal spectral type of the full
Koopman unitary is equivalent to `(ZAS1)` (discarding roots that do not occur
does not affect the asserted domination).

If `(X,S)` is a measurable factor, pullback is an isometric intertwiner
`L^2(X)->L^2(K)`.  Its image is invariant under both the Koopman unitary and
its inverse, hence reducing.  Every spectral measure in the factor is
therefore dominated by the maximal spectral type above.  Singular-continuous
measure and atoms away from roots of unity are impossible.

For a Gaussian action, the generating real representation (after
complexification) occurs as the first-chaos Koopman subrepresentation.
Choosing it with a nonzero nonatomic measure singular to circle Haar measure
would contradict the preceding domination if the Gaussian action were an
algebraic Haar factor.  This proves the Gaussian assertion as well.
