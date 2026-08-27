---
rg: 2
id: prefix-central-reducing-hull-proof
kind: route
title: Orbit the returned ranges under the corrected shared tuple inside the pulse commutant
target: prefix-central-reducing-hull-recombines-context-returns
requires:
  - finite-group-shared-overlap-polar-alignment
---

For the exact assertion, put

```text
K=closed_span{ y_(i_1)^e_1 ... y_(i_r)^e_r xi :
               r>=0, e_j in {1,-1}, xi in union_j Ran(P_j)}.
```

Because inverse letters are included, `K` reduces every `y_i`; let `Q` be
its projection.  Each `P_j<=Q`.  Since `C` commutes with every `y_i` and
contains every `P_j`, every displayed orbit vector belongs to `Ran(C)`.
Hence `Q<=C`, proving `(PCR2)`.  Repeated variables are literally the same
operator, so their compressed spectral marginals cannot depend on the
context label.

For the approximate assertion, exactify the fixed finite packet `T`.  If
`E_T` is averaging over its unitary representation, then

```text
||z-E_T(z)||_2
 <= |T|^(-1) sum_(t in T)||[z,t]||_2.                  (1)
```

Apply `(1)` to the self-adjoint part of every rounded shared involution.
Functional calculus inside the finite-dimensional algebra `T'` produces a
self-adjoint involution `zhat in T'`; the usual spectral-rounding estimate
bounds `||z-zhat||_2` by a fixed multiple of the involution and commutator
defects.  There are only finitely many generators and every context word has
fixed length, so word telescoping changes all localized BCS polynomials by
`O(sqrt(E))`.

Exactify each fixed returned child chart and use
`finite-group-shared-overlap-polar-alignment` to make its copy of every
shared involution equal to the chosen corrected global copy.  Assume, as in
the statement of the analytic lemma, that the preceding transport or
placement construction has put every returned projection under the same
corrected packet projection `C`.  Trace conservation and the fixed-table
correction then give `(PCR3)`.  Apply the exact hull construction to the
corrected tuple.  It yields `(PCR4)`.  All perturbation constants depend only
on the fixed finite packet and context menu, never on the ambient matrix
dimension.

Padding an HNN chart by `T` only makes its image commute with `T` and
preserves whatever `T`-character it already has.  It does **not** by itself
put the image under an arbitrarily chosen atom or survivor prefix `C`.  That
incidence is an input to this lemma, not a consequence of the hull
construction.
