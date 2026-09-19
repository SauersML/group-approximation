---
rg: 2
id: local-exactification-invariants-cannot-close-gluing-holes
kind: claim
title: Four open gluing holes share one residual gauge group and one disqualification test
distinct_from:
  canonical-finite-packet-data-stop-at-scalar-overlaps: that computes the exact two-subgroup overlap formula and shows those particular scalar data do not align multiplicity coordinates; this abstracts the shared residual-gauge mechanism across four different architectures and states the resulting disqualification test for candidate observables.
  gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap: that rules out one specific family of candidate observables, the integral checksums on a cokernel of repair directions; this states the necessary condition every candidate observable must satisfy, of which that family's failure is one instance.
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that is a quantitative density statement about one multiplicity polytope; this is a structural invariance statement about what independently exactified local data can and cannot determine.
  finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge: that constructs an explicit inverse twisted-regular representation neutralizing a finite groupoid cocycle; this identifies the general pattern of which that construction is the sharpest instance and applies it as a screening test.
artifacts:
  - research/artifacts/pdf-gluing-calculus-integration-2026-08-23.md
---

**ESTABLISHED.**  Four currently open endpoints in different lanes have the
same logical shape, and recognizing it supplies a cheap disqualification test
for candidate observables.

## The shape

Suppose an argument first exactifies local pieces independently, producing
separately valid local models `A_1,...,A_r`, and let

```text
N=A_1 x ... x A_r                                       (LEI1)
```

be their product.  Independent exactification never determines a point of
`N`; it determines an orbit of the group `Gamma_loc` of locally realizable
repairs — the modifications each local table already permits.  Let
`partial:N->O` record the overlap discrepancies and let `G=ker(partial)` be
the genuinely global models.  Then, tautologically but usefully:

1. any observable `Phi` computable from the separately exactified local data
   is `Gamma_loc`-invariant, hence factors through `N/Gamma_loc`;
2. if the recorded bad witness `w` lies in `Gamma_loc . G`, or more generally
   if the property `Phi` tests is preserved by `Gamma_loc` and already holds
   somewhere on `G`, then `Phi(w)` cannot certify `w notin G`;
3. therefore an observable that closes such a hole **must fail to be
   `Gamma_loc`-invariant**: it must descend to a nonzero function on the
   conductor quotient `O/partial(Gamma_loc)` and be supported on overlaps.

## The four residual gauge groups, named

The content is that `Gamma_loc` is explicitly known in each case, so (3) is a
test one can run by inspection before attempting any estimate.

| endpoint | `Gamma_loc` | recorded witness |
| --- | --- | --- |
| `globally-conditioned-v4-exit-capacity` | independent per-context transport unitaries chosen by local rounding | unrelated conjugating isometries leaving cross-Gram data unconstrained |
| `paired-same-reservoir-boundary-lemma` | the hidden multiplicity involution `V` in `t=R_f tensor V` | visible covariance relations see only conjugation, so `V=1` is not forced |
| `source-specific-pointed-rank-router-face` | tensoring with further exact zero-overlap scalar sectors | the three-factor tensor product of `(HRT1)`, exact on every ordinary relator |
| `full-packet-bicommutant-synchronization` | the relative commutant `Alg(rho_n(K))'` | the Haar-averaged `V_n` of `full-raw-packet-commutant-witness`, with `||[V_n,F_n]||_2^2>=3/8-o(1)` |

In each row the witness was produced by exercising exactly that freedom.  This
is why strengthening the local statement never helps: the local statement is
`Gamma_loc`-invariant and the witness lives in a `Gamma_loc`-direction.

## Consequences that are not tautological

- **The disqualification test is effective.**  A proposed observable is dead
  as soon as it is checked to be invariant under the named group.  Scalar
  per-context lists are invariant under per-context transport; ordinary
  relator words are invariant under tensoring with exact sectors; operators in
  `Alg(rho_n(K))` are invariant under conjugation by its commutant.  All three
  screenings are one-line checks.
- **Integral cokernel checksums are always disqualified.**  A functional on
  `Z^N/im(D)` is by construction a function of the quotient by the repair
  directions, hence `Gamma_loc`-invariant in the strongest possible sense.
  Even when the conductor quotient is nonzero, such a checksum is additionally
  subject to `gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap`.
- **The correct target is overlap-supported.**  For the commutant row this
  says the theorem to prove is not a bicommutant statement about one packet
  but a statement about which commutant modes survive the cross-root
  transition relations; that is already the formulation recorded in
  `full-packet-bicommutant-synchronization`, and this claim explains why the
  abstract finite-von-Neumann route was never going to be enough.
- **Local canonicity is not what is missing.**  In each row it is legitimate
  to make an arbitrary local choice; `unavoidable-balanced-holonomy-proof` and
  `two-oriented-trace-cyclic-returns-cancel-the-gauge` already remove the
  choice from the answer.  Effort spent forcing a canonical local gauge is
  therefore spent inside `Gamma_loc` and cannot reach the conductor.

## Limits

This is a necessary condition, not a sufficient one.  Being non-invariant on
the conductor does not make an observable matrix-only, dimension free, or
payable by ordinary word defect; those remain separate obligations.  Nor does
the criterion say the conductor quotient is nonzero in any given lane — if it
vanishes, the corresponding hole cannot be closed by any observable at all,
which is the useful negative reading of `(GCC5)`.
