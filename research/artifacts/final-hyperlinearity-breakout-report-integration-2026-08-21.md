# Integration audit: final hyperlinearity breakout report

Date: 2026-08-21.

This audit records where the supplied breakout report lives in Cairn. It is
an index, not a second copy of the mathematics. Existing claims remain the
canonical statements; genuinely new pieces were split out only when the
repository had no equivalent node.

## Dual-prefix Leavitt packet

The exact prefix pairing, common central phase, exponential Heisenberg packet,
and finite-dimensional divisibility mechanism were already present in:

- `leavitt-prefixes-form-exponential-heisenberg-packet`;
- `leavitt-prefix-heisenberg-packet-proof`;
- `affine-leavitt-steinberg-mark-is-fd-invisible`; and
- `leavitt-steinberg-quadratic-radius-pressure`.

In particular Cairn already records the stronger characteristic-`p` form and
the divisibility `p^(2^n)`, not only the binary case. The report's abstract
`W`--`W*` rank-one model is the ordinary finite Heisenberg calculation used by
those nodes; it does not need an independent route.

The matrix-chart packaging of the recursion is recorded separately as
`iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart`. It identifies
the iterated Leavitt isomorphism with the complete prefix matrix-unit system
and points to the actual missing assertion: a same-physical-reservoir or
same-corner theorem. Algebraic self-similarity by itself permits rectangular
escape.

The phase-density/cancellation-cost observation is attached to the prefix
packet and radius-pressure nodes. Its role is diagnostic: uniformly sampled
off-diagonal pairs have bounded prefix-cancellation moments, while the marked
diagonal has density `2^(-n)`; assigning the marked diagonal fixed positive
mass restores linear raw cancellation cost.

## Four-Pauli separator and common-corner target

The degree-four standard-polynomial calculation and its robust constants were
already canonical in:

- `four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap`;
- `four-pauli-pi-gap-proof`; and
- `fixed-pi-degree-fingerprints-packet-label-factor`.

The missing same-positive-corner step is already isolated by
`paired-same-reservoir-boundary-lemma` and
`common-corner-mutual-bicommutant-extraction`. The report therefore adds no
new unconditional nonhyperlinearity theorem at this point.

## Trace-promotion reductions

The solution-group central-sign reduction is already
`perfect-lcs-gap-implies-nonhyperlinear`. The stronger algebraic-corner
reduction, including the facts that the map need not be injective and the
group-algebra projection need not be central, is already
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear`.

The report's signed-Hecke cycle holonomy, finite Heisenberg type, and
projection-chart multiplicity discussion belongs to the existing
`canonical-trace-promotes-non-ce-profile` programme. The precise obstruction
is already sharper in `canonical-finite-packet-data-stop-at-scalar-overlaps`:
finite packet types determine scalar Plancherel data but leave the
multiplicity gauge and cross-chart overlap free. The warning about applying
Dye reconstruction to a bare abstract unitary-group embedding is retained in
`notes/FALSE_PROJECTIVE_UNITARY_GROUP_SHORTCUT.md`.

Finite scalar-bus/HNN couplings do not repair the forbidden-sector problem:
`scalar-bus-packet-couplings-retain-all-global-assignments` constructs exact
finite-dimensional models for every globally compatible Boolean assignment,
including forbidden assignments carrying the selected phase. Cross-
amplification makes the cycle constraints vacuous, so a genuinely
non-scalar common-carrier coupling is still required.

## Character polarization and free labels

Power polarization is already computed by `character-diracization-limit`,
and `diracization-gap-equals-nonhyperlinear-group` proves that uniform
survival of a separating non-CE gap is equivalent to the original target.
The report's raw assertion that `tau(g)^n` converges to the indicator of
`{tau=1}` is false for nontrivial unit phases (already for the sign
character). The phase-safe polarization is `|tau(g)|^(2n)`. The additional
diagonal-tensor warning is proved in
`diagonal-tensor-trace-powers-forget-full-gns-tensor`: the algebra generated
by `pi(g)^(tensor n)` can be strictly smaller than the full tensor product, so
non-CE of the latter does not imply non-CE of the former.

Free labels exhibit the complementary erasure mechanism. The tuple
`u_i tensor lambda(s_i)` has the free regular character, but the generated
tracial algebra retains only the free labels. Adjoining label erasers
recovers the coefficient algebra and simultaneously reintroduces its
noncanonical word traces. The direct proof is
`free-label-orthogonalization-erases-payload-trace`. This is a no-go for that
promotion gadget, not a no-go for analytic recovery from a positive
multiplicity corner.

## Bounded transporter fillings

The report's transporter lemma is an area statement, not a bounded-generation
statement. If every section discrepancy `h` has a uniformly bounded filling
of `[h,x_0]`, replacing contextual names by global names costs one fixed
number of cells per occurrence. Merely writing `h` as a word in finitely many
centralizing generators can still cost its word length, and spectral gap does
not supply a van Kampen filling. This distinction is wired into the existing
uniform-area Clifford/Carmichael lane. In fact
`bounded-centralizer-fillings-force-finite-stabilizer` proves a sharper
firewall for the finite-order mark used here: such a uniform bound over a
whole centralizing stabilizer exists exactly when that stabilizer is finite.
Thus the lemma is a valid conditional transporter estimate, but its premise
cannot power an infinite stabilizer merely from bounded generation or
property `(T)`.

## Arithmetic relative-commutant route

The `SL_3(Z) < SL_3(Z[1/3])` HNN candidate and its conditional
relative-commutant proof were already fully represented by:

- `non-hyperlinear-from-p3-relative-commutant-collapse`;
- `sl3-p3-pair-relative-commutant-collapse`; and
- `lambda-exact-face-closes-at-p-three`.

The exact/congruence face is not the full theorem. Genuinely uncorrectable
regular microstates remain the open sector, so the report's conditional
argument is not promoted to an established endpoint.

## Correction to the Shulman citation

The report attributes the following trace statement to Shulman:

> HS stability of `A` makes every hyperlinear trace on `A *_C A` an MF trace.

That is not Theorem 10 of arXiv:2603.13564v2. The source-verified statement is
that, for a **separable MF C-star algebra** `A` and any C-star subalgebra `C`,
the full amalgam `A *_C A` is MF in the operator-norm matrix-corona sense.
It does not assume Hilbert--Schmidt stability and it does not promote a chosen
hyperlinear trace. Cairn's canonical verification record is
`research/artifacts/shulman-2603-13564-verified.md`; the trace caveat is also
explicit in `symmetric-double-weak-mf-proof` and
`notes/FALSE_SHULMAN_TRACE_AUDIT.md`.

Consequently the proposed stable-double contradiction is not a valid theorem
from that citation. It remains only a conditional template if an independent
trace-preserving MF-promotion result is supplied. The correction is a Cairn
claim with proof at `shulman-symmetric-double-has-no-stable-trace-upgrade`.

## Net frontier after integration

The dual-prefix construction is exact and its finite-dimensional
annihilation theorem is complete. It still cannot be upgraded formally from
exact representations to normalized-Hilbert--Schmidt microstates;
`exact-fd-invisibility-has-no-general-hs-robustification` gives an explicit
sofic counterexample to any structure-free upgrade.

For the Leavitt lane, the sharp missing statement is same-reservoir control
for the iterated matrix chart, equivalently a positive-density common-corner
implementation that blocks rectangular escape. For the trace-promotion lane,
the missing statement is a finite group-word compiler that fixes the entire
forbidden BCS face rather than only scalar packet masses. Neither gap is
silently promoted to a proof of a nonhyperlinear group.

## Post-audit contraction of the Leavitt seam

Subsequent attacks substantially reduced, but did not close, the
same-reservoir problem.

`one-coarse-to-fine-prefix-isometry-closes-the-reservoir` proves that one
operator from a coarse `M_2` atom to a fine `M_4` atom already has normalized
Gram defect at least one quarter of the common carrier trace. The exact
Leavitt completeness model supplies `x=s_(00)t_0`, `y=s_0t_(00)`, whose
partial swap is the fixed three-root word `E_12(x)E_21(y)E_12(x)`.

The analytic decoder is now complete. By
`unitary-offdiagonal-block-gram-is-support-leakage`, for projections `e,f`
and a unitary word `J`, the block `X=fJe` obeys

```text
e-X^*X=((1-f)Je)^*((1-f)Je).
```

If the carrier reflections are words, the one support word
`R_f J R_e J^*` controls this Gram defect. Even that block can be discarded:
`coarse-fine-selector-covariance-has-quarter-trace-floor` gives directly

```text
||J e J^*-f||_2^2 >= tau(P)/4.
```

Thus the remaining positive target is exactly one mixed selector-support
moment, not a mutual bicommutant, a four-Pauli placement theorem, or a family
of Morita arrows.

Three sharp firewalls delimit this target.

- `literal-prefix-three-root-swap-retains-typed-carriers` gives an exact
  finite countermodel in which the word swaps separately typed equal-rank
  leaves while the coarse and fine packet identities remain unrelated.
- `controlled-pauli-corner-has-clifford-groupification` realizes the fine
  atom reflection only as `CZ tensor V`, with an arbitrary multiplicity
  involution `V`; the support row sees `V` even though conjugation covariance
  does not.
- `pure-prefix-swap-invariants-are-selector-blind` proves that spectrum,
  power traces, determinant, multiplicity, and rectangular index cannot
  remove this ambiguity. The first useful scalar is necessarily the mixed
  moment `tau(e)-tau(fJeJ^*)`.

The algebraic-frame alternative is also closed:
`algebraic-selector-mixing-frame-collapses-forbidden-sector` shows that a
universal tight frame plus exact selector mixing kills the forbidden sector
in every representation, contradicting completeness. Hence any successful
support-moment estimate must use finite external multiplicity or a genuinely
canonical-microstate selection.

Finally, the exact Nielsen compact-cocycle annihilation theorem has no
structure-free quantitative upgrade.
`sofic-nielsen-charts-defeat-uniform-compact-collapse` constructs commutative
finite-dimensional asymptotic models with vanishing local action/covariance
defect while the killed mark stays at distance `sqrt(2)`. A positive Nielsen
route must therefore use the specific nonsofic/Kazhdan geometry of its
compressor, not compactness alone.

The same-reservoir hypothesis can now be removed altogether at the analytic
endpoint.  `cyclic-coarse-fine-selector-rows-spread-carrier-error` proves that
for arbitrary carrier masses, arbitrary unitaries (including independent
multiplicity twists), coarse halves `e_i`, and fine quarters `f_i`,

```text
sum_i ||U_i e_i U_i^*-f_(i+1)||_2^2
  >= (1/4) sum_i tau(P_i).
```

The signed trace deficits telescope around the cycle before absolute values
are taken.  This is the desired error-delocalization mechanism: moving the
defect into the next reservoir cannot dilute it after one full return.  The
properly infinite Leavitt model realizes every row exactly, so completeness
survives.  What remains is solely matrix-only authentication of the selector
reflections; the cycle no longer needs a common carrier or gauge alignment.

`global-marked-type-cycle-selector-decoder` now connects this trace ledger to
the non-CE BCS source. A global permutation of all `(context, marked type)`
sectors decomposes into selector cycles; isotypic orthogonality packs their
compressed row energies with a loss depending only on the fixed number of
contexts. The final construction has exactly two matrix-only obligations:
ordinary actuator energy must dominate the **sum** of type-compressed mixed
rows, and the decoded carriers must globally cover a fixed fraction of the
shared forbidden BCS mass. No individual context or type needs positive
mass, and no row is asserted as a universal identity.

Two further audits sharpen the syntax. Quasi-regular coset modules can make
a literal involution quarter-negative, but
`hecke-quarter-selector-is-untyped-or-rank-preserving` shows the
dichotomy: without type authentication the regular sector is balanced, while
after authentication every ordinary HNN/Hecke edge preserves the very
multiplicity that a coarse-to-fine row must change. Conversely,
`recursive-clifford-tail-supplies-anchor-but-not-contraction` constructs the
desired identity-outer Clifford anchor exactly: the parent tail gate is the
local `CZ` times the two child tail gates, so the child product carries the
same multiplicity gauge and cancels it. Finite Clifford truncations remain
stationary, however. Self-reference solves gauge coherence but supplies no
strict contraction; a payload-dependent first-hit/proper-corner exposure law
is still required.

The coverage half of the global decoder is now solved.
`forbidden-weighted-type-carrier-coverage-is-rank-rounding` trims each marked
forbidden type projection to the largest rank divisible by four. Over the
fixed menu the total loss is at most `3|Omega|/d`, and every retained carrier
has exact analytic half/quarter selectors. Thus global coverage holds with
coefficient one; only summed-row domination remains. The carriers need not
reduce the context packet, and an explicit isotypic counterexample shows that
requiring reduction would reintroduce the old alignment problem.

The recursive lane also has its strict analytic exposure.
`tail-wordized-child-surplus-collision-supplies-rct7` uses the fact that every
forbidden BCS copy contributes one surplus corrected child. Returning the
full child to the next carrier gives

```text
(1+beta)a_n <= a_(n+1)+boundary+one support-row energy,
```

so the contraction factor is `lambda=(1+beta)^(-1)<1`. The recursive
identity-outer anchor cancels the multiplicity gauge after a corrected child
has been selected, and one reflection conjugacy relator then controls the
leakage. It does not itself wordize the selector-controlled aggregate child:
`aggregate-child-wordization-three-route-no-go`
also rules out treating the Toeplitz proper isometry as a group unit or
multiplying the finite decoder menu. Stationary Clifford truncations now
pay exactly the forbidden surplus, while the perfect model has zero surplus
and admits an exact HNN return. The remaining task on this lane is a genuinely
finite-matrix-only selected-sector/orthogonalization step that wordizes the
aggregate corrected child from the shared BCS tuple, not another analytic
contraction lemma.

Finally, `one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum` proves
that one uncompressed closed transport word cannot supply the remaining
summed-row domination: the last multiplicity gauge always closes the
holonomy while the cyclic selector floor stays positive. A positive actuator
must compress intermediate stages by the analytic forbidden cuts or impose a
genuinely matrix-coordinate condition that removes that last-edge gauge.

The two-cell follow-up is now exact.
`compressed-k2m-locks-gauge-but-needs-matrix-separator` replaces the single
cycle by `K_(2,m)`: its `m-1` rectangle words synchronize every column gauge,
and orthogonal source compression gives

```text
source trace-capacity trace <=2(rectangle energy+compressed leakage).
```

For the three eight-slice failures this left side is exactly
`tau(P_f)/16`. Thus rectangles solve the last-gauge problem, but not GTC4:
uncompressed row-column factorizations keep all squares exact, while making
the leakage a universal reflection relator contradicts the regular trace.
The remaining actuator is sharply one matrix-only shared-BCS bound on the
compressed leakage; no further multiplicity synchronization is missing.

## Computer-science and quantitative-no-go audit

The proof-system framing is retained in corrected form in
`computer-science-framing-audit-2026-08-21`.  The rigorous computability
statement is

```text
finite-presentation HYP in Pi^0_2,
finite-presentation non-HYP in Sigma^0_2,
```

proved by `nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound`.
This is an upper bound, not a matching hardness theorem and not an RE
enumeration of nonhyperlinear presentations.  The tensor/direct-sum
normalization needed to pass from separately separating finite word tests to
one simultaneous near-canonical microstate is included in the proof.  The
productive interpretation is that a successful compiler needs perfect exact
tracial completeness and dimension-independent finite-matrix soundness.  It
is analogous to a perfect-completeness quantum PCP for group words, but it is
not the standard quantum PCP conjecture: dimensions are unbounded and the
complete witness may exist only in a non-CE tracial algebra.

The three proposed quantitative obstructions are audited in
`section-three-quantitative-no-go-audit-2026-08-21`.  Nonzero finite
predicate projections have positive twisted-regular trace, so universal
tracial group relators cannot delete nonlinear selector atoms.  A
supercritical Clifford challenge has the conditional critical row scale
`Theta(1/sqrt(log d))` only after a dimension-uniform complete-table decoder
and positive-density corner have been supplied; those hypotheses are not
currently consequences of the local Clifford presentation.  The scale itself
is sharp even inside one Clifford factor:
`dirac-average-is-a-sharp-near-extra-clifford-generator` proves that the
normalized sum of `2m` exact anticommuting generators is an exact involution
whose anticommutators with the generators have size `sqrt(2/m)` and whose
anticommutator with chirality is zero.  Its coefficient `l1` mass is exactly
`sqrt(2m)`, so a constant-loss word-telescoping decoder cannot be hidden in
that expansion.  Finally,
block-diagonal exact models leave the whole block-scalar algebra in the
adjoint Laplacian kernel, so a scalar spectral gap inside every block does not
localize coherent normalized-HS error.  These are fences around the native
gap/fault-tolerance lane, not a proof of its missing HS-to-site-noise bridge.

The recursive tail itself is no longer a syntax problem:
`free-cone-shift-finitely-wordizes-recursive-clifford-tails` gives a fixed
four-generator presentation, linear addressed tail words, and one-cell
recursion and anchor diagrams.  The remaining recursive obstruction is only
the selector-controlled aggregate child.  The tail cancels its multiplicity
gauge after selection; it does not perform the selection.

## Optimizer, arithmetic HNN, and exit audit

The bounded PSL2 optimizer is retained only as the heuristic artifact
`psl2-far-sector-optimizer-heuristic-2026-08-21`: exact torsion is controlled,
but the short odd-power diagnostic is not distance from all congruence
representations and the smoke residual is not a lower-bound certificate.
The separately supplied augmented-Lagrangian data are quarantined as
`user-reported-augmented-lagrangian-hnn-probe-2026-08-21`. They report
BS(2,3) calibration/control rows and congruence-seeded projective-HNN floors
`.048`--`.076` for primes `7` through `31`, but were not rerun, are
nonmonotone in this range, and use a different mark-separation objective.
The ambiguous “trivial `(relator)^2`” calibration label is preserved with a
normalization warning rather than treated as a verified certificate.

The arithmetic candidate is audited in
`sl2-hnn-iwahori-dynamical-fork-2026-08-21`. The four-generator,
seven-relator presentation is the projective `PSL_2` HNN and is an explicit
non-MAP control group. The currently wired conditional nonhyperlinearity
route uses the `SL_2` HNN; no central-quotient stability transfer is assumed.

The three proposed exits remain logically distinct. A native perfect LCS gap
would finish through `perfect-lcs-gap-implies-nonhyperlinear`, while imported
fault tolerance still needs the HS-to-site-noise bridge. Soficity of the
Bruhat--Tits coset action would refute Iwahori stability, but nonsoficity is
only a one-sided failed-countermodel result. The characteristic-two
Kaplansky fork requires both a direct-finiteness failure in the Leavitt unit
group algebra and a presently unknown hyperlinear-to-directly-finite theorem;
it is not a current route to the goal.
