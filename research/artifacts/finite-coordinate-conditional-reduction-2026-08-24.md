# The finite-coordinate conditional reduction of the Leavitt non-MF theorem

**Ingested 2026-08-24.**  Source: an external pair of documents handed to this
session -- a conditional-reduction manuscript, *A finite-coordinate route to a
finitely generated simple non-MF group*, and the audit that produced it,
*Can the main Leavitt manuscript be made property-(T)-free?*  This file records
the section-by-section map onto existing nodes, the one lemma that was new,
and two corrections to the audit.

## Verdict

The manuscript is an honest conditional reduction and it is almost entirely a
repackaging of material the graph already carries.  Exactly one of its
ingredients was missing from the graph as a node, and it was already
kernel-checked in the Lean development without a node citing it.

The reduction is stated for `H = EL_12(R)`, `R = L_(F_2)(1,2)`, whereas the
graph's operator-norm route runs in `St_20(R)`; the two are wired to the same
open hypothesis and the difference is discussed below.

## Section map

| manuscript | graph |
|---|---|
| Prop. 1.1, MF residual calculus | `universal-mf-quotient` |
| Thm. 2.1, finite-dimensional commutant rigidity | `compression-defect-dies-in-finite-dimensions` |
| Lem. 3.1, `EL_n(A)` finitely generated | **was missing** -- now `elementary-group-fg-from-fg-coefficient-ring` |
| `p+q=1`, `t_1 q s_1 = 1`, `q != 0` | `full-leavitt-idempotent-defect-saturation` |
| §3.2, the Whitehead compressor and `tau L tau^{-1} <= L` | the compression lane, `hilbert-hotel-model-is-unconditionally-non-mf` |
| Prop. 3.2, `H` simple | `binary-leavitt-elementary-group-is-simple` |
| Prop. 3.3, `d = e_02(q)` is an involutive normal generator | `full-leavitt-idempotent-defect-saturation` |
| Lem. 4.1, rank-deficient return row | `rank-deficient-return-row-has-operator-norm-one` |
| §4.1, `yx = e_00`, `xy = f_(00,00)`, the three-elementary word | `one-coarse-to-fine-prefix-isometry-closes-the-reservoir` |
| Hyp. 4.2, common-carrier recovery | `opnorm-leavitt-coarse-fine-return-row` (OPEN) |
| Thm. 4.3, common carrier implies MF collapse | `authenticated-coarse-fine-return-forces-mf-collapse` |
| Cor. 5.1, finite-dimensional linear triviality | `compression-defect-dies-in-finite-dimensions` + normal generation |
| Cor. 6.1, `R^x` and every `GL_n(R)` | `binary-leavitt-all-ranks-full-mf-radical`, `leavitt-gl-equals-el-and-perfect-unit-group` |
| §7, prescribed MF quotients, `W_Q = H *_A (Q x A)` | `full-mf-radical-absorber` clause 4 |
| §8, no normalized-HS ledger can supply the row | `opnorm-return-row-cannot-come-from-an-hs-ledger` |
| §8, exactification is not the obstacle | `opnorm-packet-exactification-is-dimension-free` |
| §8, spectator-multiplicity trading | `rectangular-escape` |
| audit, no functorial group-algebra selector | already the *selector* attempt inside `opnorm-leavitt-coarse-fine-return-row` |
| audit, the naive replacement is false | `bare-self-copy-mf-calibration` |

## The one new ingredient

Lemma 3.1: if a unital ring `A` is generated as a ring by a finite set `X`,
then `EL_n(A)` is finitely generated for every `n >= 3`, by the finitely many
`e_ij(y)` with `y in X union {1}`.  Addition is produced inside one root
subgroup by `e_ij(a)e_ij(b) = e_ij(a+b)` and multiplication across roots by
`[e_ij(a),e_jk(b)] = e_ik(ab)`; the set of coefficients whose root matrices
lie in a fixed subgroup containing all `e_ij(1)` is therefore a subalgebra,
and it contains `X`.

This was already kernel-checked as `elementaryGroup_finitelyGenerated` in
`GroupApproximation/Leavitt/ElementaryGroup.lean` -- whose docstring names a
manuscript label `lem:elfg` that no `.tex` in the repository defines -- and no
node cited it.  It is now `elementary-group-fg-from-fg-coefficient-ring`.

Its point is dependency removal: the printed manuscript obtains finite
generation of `H` as a by-product of the Ershov--Jaikin-Zapirain property-(T)
theorem for `EL_n` over a finitely generated ring.  With the lemma, finite
generation costs no rigidity input at all.

## Correction 1: the audit mislocates the second essential (T) use

The audit reports one essential use of property (T) -- the asymptotic
commutant transport of `\thm:transport` -- and describes the manuscript's
Section 4 as an active-core/torsion bridge independent of (T).  That is not
the current printed Section 4.  `non_mf_groups_exist.tex` §4 is *The canonical
Kazhdan sector and the MF radical*, whose `thm:normal-kazhdan` takes a normal
property-(T) subgroup as a hypothesis and runs the Kazhdan projection
argument.  So the printed text has **two** essential (T) steps, §3 and §4, and
the conditional reduction replaces both of them at once with the single
finite-coordinate hypothesis.  The audit's dispensability finding for finite
generation stands; its count does not.

## Correction 2: the audit's description of Route C is behind the graph

The audit lists operator-norm exactification of the fixed packets as part of
the missing hypothesis and describes the operator-norm lane as a smaller
version of the Hilbert--Schmidt one.  Both were already corrected in the graph
on the same day: exactification is free
(`opnorm-packet-exactification-is-dimension-free`) and the operator-norm row
is *smaller in scope but strictly stronger in norm*, so no HS estimate can
ever be recombined into it (`opnorm-return-row-cannot-come-from-an-hs-ledger`).
The residue is the single additive statement `sum_i e_ii ~ sum_a f_aa`, which
a Steinberg/root presentation cannot state.

## Rank twelve versus rank twenty

The manuscript's `H = EL_12(R)` is simple, so its normal-generation step is
just `d != 1` plus `binary-leavitt-elementary-group-is-simple`, where the
graph's route through `St_20(R)` spends
`full-leavitt-idempotent-defect-saturation` on an explicit root computation.
Both are available and neither is on the critical path: the hole is the same
one either way.  No node was added for the rank-twelve packaging, because the
row hypothesis as stated in `opnorm-leavitt-coarse-fine-return-row` is written
for the `St_20(R)` presentation and an `EL_12` restatement would be a
near-duplicate open claim, not a reduction.

## What was deliberately not added

No node for the prescribed-quotient amalgam `W_Q = H *_A (Q x A)`: it is an
instance of `full-mf-radical-absorber` clause 4, and the direct product
`H x Q` already realizes the same Hom-set bijection.  No node for the
prefix-code isomorphism `M_n(R) ~= R`, which is inside
`leavitt-gl-equals-el-and-perfect-unit-group`.  No citation node for
Preusser, Abrams--Aranda Pino, Ara or Aranda Pino--Crow, all of which are
already carried by `binary-leavitt-elementary-group-is-simple-proof`.
