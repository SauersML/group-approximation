# The raw packet collapses on the classical spherical branch

Date: 2026-08-13

## 1. Question tested

Let

\[
 G=GL_4(2)\cong A_8,
 \qquad H=\operatorname{diag}(GL_3(2),1),
 \qquad B=G*_H G.
\]

The two atlas charts define the classical boundary quotient `B`.  The
nonincident-flag calculation decomposes the right-`H` spherical module as

\[
 \operatorname{Ind}_H^G(1)=1\oplus14^{\oplus2}\oplus35\oplus56.
 \tag{CSR1}
\]

Because the 35- and 56-dimensional constituents have multiplicity one, it
was tempting to project the compiled raw swap, comb, and hard class-11 pair
to these scalar channels and look for a gauge-independent child-versus-parent
index.  The prerequisite is that the packet have a nontrivial closed
holonomy in the classical amalgam.

The prerequisite fails exactly.

## 2. Exact normal-form result

Transport the source words by the certified inner alignment and reduce them
by the standard normal-form algorithm for `G *_H G`.  The exact results are

```text
word                         source length   amalgam normal form
raw swap                          25         identity
comb compressor                  175         identity
hard class-11 prefix               2         one element of H
hard class-11 next letter          1         one element of H
```

For the hard pair, the two surviving matrices are

```text
prefix:      01010000000101000000010000000001
next letter: 01000000010100000000010000000001
```

and both lie in the literal block subgroup `H`.  Conjugating the four
generators `E01,E10,E12,E21` of `H` by each of the four packet words also
returns an element of `H`.  For the raw and comb words this normalizer check
is tautological after their complete reduction, but it independently audits
the word orientation and alignment used by the script.

Thus, in `B`,

\[
 r_{\mathrm{src}}=u_{\mathrm{src}}=1,
 \qquad q_{\mathrm{src}},\ell_{\mathrm{src}}\in H.
 \tag{CSR2}
\]

This is an exact finite-group/amalgam calculation, not a numerical matrix
experiment.

## 3. Consequence for the spherical attack

Equation `(CSR2)` kills the direct classical spherical test.  On every
representation of the aligned amalgam, the raw and comb holonomies are the
identity and the hard pair acts through the already identified edge group
`H`.  In particular, the scalar 35 and 56 channels cannot retain the
properly-infinite two-child sign or index at this boundary point.  Passing to
the repeated 14-dimensional doublet does not repair the zeroth-order
collapse: its `U(2)` multiplicity gauge acts only after the same amalgam
identity has already been imposed.

This does **not** say that the source words are identities in the Leavitt
atlas group.  Their scalarized Leavitt values are the nontrivial raw
compressors.  It says precisely that their nontriviality is transverse to
the classical `H`-amalgam quotient.  The classical quotient forgets the
coefficient data which distinguishes the Leavitt branch.

The result fits the existing universal first-order no-go.  We now have both:

1. zeroth-order collapse of the complete raw packet at the classical fold;
2. vanishing of every fixed-fold square-zero obstruction over every field.

Consequently a successful recovery theorem cannot be a fixed spherical
character, a first derivative, or a formal infinitesimal deformation of the
classical alignment.  It must use a genuinely nonlinear, nonperturbative
feature of matrix microstates which remain away from that fold.

## 4. Revised live endpoint

The source compiler remains essential: it gives literal finite words whose
normalized Hilbert--Schmidt behavior can be tested in any two-chart
microstate.  What is no longer live is projecting those words through the
fixed aligned flag representation before extracting coefficient data.

The next valid route must instead begin with the nonclassical branch.  In a
hypothetical zero-defect matrix sequence, the existing Reynolds-gap result
forces the relative chart intertwiner to remain a fixed distance from the
`H`-aligned locus.  One must use the raw and comb relations at that
misaligned point to recover finite coefficient arrows, and only then take
gauge-invariant ranks, singular values, or a one-cut leakage index.  A fixed
classical spherical projection has already discarded exactly those arrows.

A concise revised target is:

> Condition on the certified Reynolds misalignment, express the compiled
> raw packet in the resulting finite `H`--`H` bimodule quiver, and prove that
> its nonlinear block products contain either two isometries with orthogonal
> ranges or a one-cut unitary leakage imbalance.

Any derivation which substitutes the aligned `1+2(14)+35+56` module before
this nonlinear extraction repeats the falsified calculation above.

## 5. Replay

The audit script is

```text
experiments/atlas_raw_compressor_amalgam_audit.py
```

and its complete exact output is

```text
experiments/atlas-raw-compressor-amalgam-audit.json
```

It consumes the committed source-word artifact and the previously certified
alignment.  Replay on MSI with one core:

```text
module load python3/3.12.4_anaconda2024.06-1_libmamba
PYTHONPATH=experiments \
  python3 experiments/atlas_raw_compressor_amalgam_audit.py \
  > experiments/atlas-raw-compressor-amalgam-audit.json
```

