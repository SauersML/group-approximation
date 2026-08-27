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
There is one safe part of the center which need not be reset.
`fanizza-doubling-carriers-form-orthogonal-flag` proves that the derived
carrier and first-hit signs already commute in the exact source algebra and
obey a literal word recursion.  A partial-center endpoint may therefore keep
that one carrier flag.  It must still discard the original context selector
center, and `(FOF5)` shows that the overlap projection—not the affine word
recursion—is the remaining nonlinear payment.
The earlier raw branch-controlled reset does not supply this step:
`raw-schur-generator-is-not-child-center` shows that the raw `q_(N+1)`
eigenspaces are not the child-simple branches.  The corrected branch signs
can nevertheless be paired by the ordinary finite semidirect product of
`schur-child-center-sign-flip-is-group-automorphism`, which acts by
`q_(N+1)->Jq_(N+1)` and hence sends `Q_f->JQ_f`.  What remains before applying
`hnn-selector-chart-transport-preserves-mark-and-types`: an HNN edge makes
the post-reset chart conjugate to the next Fanizza context and gives the
type-vector part of `(TCM1)` without asserting equality or commutation—is a
genuine reset/transport of the **old selector character**.
`translation-symmetrized-schur-child-reset` now supplies that reset by
permuting shifted-pencil copies while translating all selector signs. Thus
the local complete-type reset is solved. What remains here is its coherent
placement in the Toeplitz tail together with the inactive-sector payment of
clause 3; a finite graph of the reset groups alone would still have stationary
regular type flow.
The stationary space is no longer mysterious:
`symmetrized-reset-collapses-schur-flow-to-one-ray` proves it is exactly one
scalar ray and that all transverse type-vector leakage already costs
`C sqrt(E)`. The live Toeplitz estimate therefore only has to make this one
scalar current contract or enter a summable residual carrier.
Moreover `translation-symmetrized-full-schur-reset` puts the full gate and
reset in one finite group. It may therefore occupy one bounded Toeplitz head
which centralizes the next deep tail; no local free-product amalgam has to
cross the head/tail boundary.
The local wall is now explicit as well:
`symmetrized-full-reset-forces-fixed-reynolds-density` gives

```text
rank(E_C-E_B)/d^2=1/(2^(k+2)D^2).
```

Thus the missing recurrence estimate does not have to create positive
density. It only has to prove a survive-or-recurse law for this fixed wall,
with the recurse branch acting on the sole `m`-dimensional multiplicity space
capable of erasing it. This wall is structural rather than predicate-sensitive;
the return must additionally couple its orientation to the surplus `2K_1n`.

That scalar multiplicity channel already carries a sharp one-sided Gram
escape.  `translation-reset-leaves-a-compressed-gram-spectator` constructs,
on an exact amplification of the reset ray, a chord with
`E-X^*X=E_0 tensor Q` and `tr(E-X^*X)=tr(H)=1/8`.  All addressed old-spin
Pauli incidences remain exact.  Hence neither the reset nor coordinate
localization forces the Gram into the finite label algebra.  Any proposed
version of clause 3 through the compressed-Gram route must include one mixed
chord--reset relation which acts nontrivially on the scalar multiplicity
factor; type-vector balance and the fixed Reynolds wall alone leave this
zero-defect spectator.

Imposing full finite-label covariance on that chord is not the missing
relation.  By `full-label-chord-normalization-kills-the-hilbert-hotel`, two
or more fixed transverse charts which generate the label factor force the
chord to be `u_0 tensor U_res`.  This removes the Gram spectator with a
dimension-free mixed-word floor, but also prevents the proper infinite
one-sided return.  More generally, any fixed-chart covariance strong enough
to return both support cuts to its finite label algebra preserves their
finite rank deficit; weaker covariance leaves the Gram unauthenticated.
The clause-3 payment must therefore be genuinely finite-multiplicity
sensitive rather than a fixed chart normalizer.

Weakening to Toeplitz range covariance preserves completeness but not
soundness.  `toeplitz-range-commutator-has-a-balanced-mirror-exit` takes
`E=F+H` and an exact finite conjugate `TET^*=F+C` with
`tr(C)=tr(H)>0`.  The source/range reflections commute exactly and all
old-spin incidences can remain exact, while `C` is the scalar-ray mirror
exit.  Finite trace only balances `H` and `C`.  Hence a range-reflection
commutator cannot provide clause 3; one must wordize or otherwise pay the
oriented block `(1-F)TE`, which is precisely the additive corner datum lost
by the ordinary word.

There is a cleaner predicate-sensitive observable than the bare Reynolds
rank. By `schur-predicate-is-character-density-difference`, every local
forbidden projection satisfies

```text
P_f=2D(Z_C-Z_B),
tau(P_f)=4D^2||Z_C-Z_B||_2^2.                         (TCM3)
```

Both `Z` terms are explicit fixed character-table averages of packet words.
Therefore an acceptable proof of `(TCM1)` may return these density elements
directly through the Toeplitz corner, rather than transporting anonymous
irreducible copies or the entire adjoint Reynolds range.
The substitution theorem
`fanizza-schur-density-substitution` shows
that the original polynomial recurrence accounting survives this replacement.
Accordingly the exact remaining Toeplitz estimate is the bounded-overlap law

```text
sum_c||Z_(C_c)-Z_(B_c)||_2^2 <= C_ret E_group,
```

or a contractive residual version of the same inequality.
By `schur-density-gap-has-no-direct-relator-certificate`, this cannot be a
direct telescoping identity for each gap. The Toeplitz/property-`(T)` stage
must be used essentially as a finite-dimensional-only rigidity theorem.

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
  `binary-schur-child-toeplitz-self-embedding` now gives an explicit choice:
  it replaces the Toeplitz generator by its square and uses the resulting
  two-site head as the old relative-Pauli matrix coordinate.  Sectorwise the
  map is `M_(2D)->M_2(M_D direct_sum M_D), a |->(a,a)`, so it retains the
  corrected child sign and adds the two child multiplicities exactly.  Thus
  the exact placement is closed after collapsing the allowed ideal to the
  augmentation.  The remaining analytic statement is
  `binary-schur-toeplitz-one-branch-hs-payment`: one retained sign must pay
  ordinary relator energy rather than participate in stationary regular flow.
- Put the next full packet in the old external commutant: invalid unless a
  center reset is included. It forces every future selector to commute with
  every past selector and fails the mandatory contextuality test.
- Raw branch-controlled Pauli reset: invalid for Schur child types, because it
  balances raw `q` spectra.  The corrected child sign flip is now solved by a
  genuine child automorphism, and the translation-symmetrized overgroup resets
  the full selector-labelled vector.
- HNN selector-chart transport closes the type-vector estimate only after a
  valid old-selector reset has supplied two isomorphic endpoint charts.
  It deliberately preserves multiplicity; the factor two has already been
  created by child restriction. The live calculation is only the leakage
  bound for inactive Fanizza sectors.
