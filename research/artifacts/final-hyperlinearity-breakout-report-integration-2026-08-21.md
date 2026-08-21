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

## Character polarization and free labels

Power polarization is already computed by `character-diracization-limit`,
and `diracization-gap-equals-nonhyperlinear-group` proves that uniform
survival of a separating non-CE gap is equivalent to the original target.
The additional diagonal-tensor warning is essential: the algebra generated
by `pi(g)^(tensor n)` can be strictly smaller than the full tensor product, so
non-CE of the latter does not imply non-CE of the former.

Free labels exhibit the complementary erasure mechanism. The tuple
`u_i tensor lambda(s_i)` has the free regular character, but the generated
tracial algebra retains only the free labels. Adjoining label erasers
recovers the coefficient algebra and simultaneously reintroduces its
noncanonical word traces. This is a no-go for that promotion gadget, not a
no-go for analytic recovery from a positive multiplicity corner.

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
trace-preserving MF-promotion result is supplied.

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
