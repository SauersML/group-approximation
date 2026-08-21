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
