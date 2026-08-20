---
rg: 2
id: toeplitz-schur-child-masa-recurrence
kind: claim
title: Toeplitz tails return each active Schur child MASA as the next controlled packet input
distinct_from:
  schur-child-toeplitz-morita-wire: that computes the exact local two-child multiplicity algebra; this must place successive controlled packets in that algebra with quantitative normalized-HS control.
  toeplitz-tail-retains-contextual-schur-density: that asks for a generic survive-or-recurse dichotomy for a local Reynolds wall; this asks only for the oriented Fanizza tape and may use its polynomial decomposition identities.
---

In the diagonal-covariant Toeplitz/Fanizza skeleton, choose the fixed packet
embeddings so that for every level `n` the following holds after uniform
relative exactification.

1. Restriction to the `Q` child of cell `n` produces the two canonical branch
   types of `oriented-schur-child-branching-identity`, and their total weighted
   multiplicity is the input carrier for cell `n+1`. The relative Pauli
   `C^2` is therefore retained as a branch label rather than discarded into a
   spectator factor.
2. The complete weighted type vector of that child carrier and the input type
   vector of cell `n+1` differ by at most

   ```text
   C(n+1)^k sqrt(E).                                           (TCM1)
   ```

3. The transverse `P` child is recovered by the single Toeplitz head actuator.
   Every inactive sector in the Fanizza `(FDB1)` decomposition either enters
   the same discrepancy `(TCM1)` or pays a named relator with total
   bounded-overlap cost `C(n+1)^k sqrt(E)`.
4. The infinite amplified marked BCS representation extends across all these
   child/tail incidences, so the resulting finite presentation retains a
   nonidentity marked word.

Clause 1 must not put the entire next packet algebra in the literal commutant
of the previous `A_n`. By
`nested-schur-multiplicity-wire-globalizes-selectors`, that would commute all
past and future selector centers and reduce the tape to a classical history.
The required placement must carry the two `q_(N+1)` branch labels while
resetting the old selector center—for example through a partial-center
endpoint chart or projective child holonomy.

Combined with the oriented child-branching identity, `(TCM1)` gives

```text
a_n <= (1/2)a_(n+1)+C'(n+1)^k sqrt(E),                         (TCM2)
```

with no scalarization of a nonlinear projection and no termwise conjugacy of
nonisomorphic finite packet groups.

## Attempts

- Identify the full output packet with the next input by an HNN edge: ruled
  out by `hnn-conjugacy-cannot-return-schur-morita-multiplicity`.
- Use only the compressed child/full inclusion: residual tail action can erase
  its Reynolds density. The surviving design must use the actual child
  commutant as the next input carrier, not merely assert that both finite
  subgroups lie in the ambient compressor.
- The exact local algebra is solved by `schur-child-toeplitz-morita-wire`.
  The remaining calculation is to choose the self-similar packet embeddings
  so the tail copy uses that particular relative `C^2` factor and to prove
  `(TCM1)` from the shared word defects.
- Put the next full packet in the old external commutant: invalid unless a
  center reset is included. It forces every future selector to commute with
  every past selector and fails the mandatory contextuality test.
