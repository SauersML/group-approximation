# The raw compressor packet now has explicit two-chart source words

Date: 2026-08-13

## 1. Outcome

The properly infinite packet in
`TRUE_RAW_COMPRESSOR_PROPERLY_INFINITE_PACKET.md` used two explicit Leavitt
units:

* the scalarized raw swap `r`; and
* the scalarized comb compressor `u`.

Until now they were explicit as matrices over the binary Leavitt algebra but
not as words in the two finite `A8` atlas factors.  That prevented a literal
representation-type calculation: evaluating a printed ring matrix in an
arbitrary unitary atlas model is exactly the coefficient-recovery step which
must not be assumed.

The new exact compiler produces reduced free-product words

```text
r_src in A8 * A8,       length 25,
u_src in A8 * A8,       length 175,                         (RCS1)
```

with

\[
 \rho(r_{\rm src})=r,
 \qquad
 \rho(u_{\rm src})=u
 \tag{RCS2}
\]

under the concrete Leavitt atlas quotient.  The raw word uses only six
distinct factor elements, and the comb word uses 28.  Both identities were
verified by exact all-depth prefix reduction on MSI.

This closes a real bookkeeping gate: the raw packet can now be evaluated in
every canonical two-chart unitary model using only the two finite chart
representations and their relative unitary.  No ring entry is inserted by
hand.

It does **not** yet recover the characteristic-two projections `p_11` and
`p_001` in a matrix model, and therefore does not yet prove
nonhyperlinearity.

## 2. Compiler

Use the three-leaf atlas code

```text
Gamma=(00,01,1)
```

and the depth-two scalarization code

```text
C=(00,01,10,11).
```

A rank-four elementary transvection scalarizes to

\[
 x_{ab}(c)\longmapsto
 1+C_a c C_b^*.
 \tag{RCS3}
\]

Every monomial summand in `(RCS3)` is a scalar prefix transvection
`1+alpha beta*`.  If `alpha=Gamma_i mu` and
`beta=Gamma_j nu` with `i!=j`, it is the atlas root

\[
 x_{ij}(s_\mu t_\nu).
 \tag{RCS4}
\]

Products in the coefficient of `(RCS4)` are compiled recursively with the
Steinberg identity

\[
 [x_{ik}(a),x_{kj}(b)]=x_{ij}(ab).
 \tag{RCS5}
\]

The leaves `Gamma_i` are a prefix code, so if `alpha` and `beta` lie below
the same base leaf, choose a different `Gamma_k` and use

\[
 1+\alpha\beta^*
 = [1+\alpha\Gamma_k^*,1+\Gamma_k\beta^*].
 \tag{RCS6}
\]

The leaves in the two factors allocate every one-letter root exactly as in
`EXPLICIT_LEAVITT_ATLAS.md`; the existing `q(i,j,a)` routine supplies those
thirty roots.  Equations `(RCS5)--(RCS6)` therefore compile every
transvection appearing in the printed rank-four words.

For the raw swap, the compiler translates its three transvections.  For the
comb it translates the twelve factors

```text
x_3i(t0+1) x_i3(1) x_3i(s0+1) x_i3(t0),  i=2,1,0.     (RCS7)
```

Characteristic two turns addition in `t0+1` and `s0+1` into multiplication
of same-root transvections, so `(RCS7)` uses group multiplication only.

## 3. Exact next calculation

This calculation has now been completed, with a negative result for the
direct classical projection.  Both compiled compressor words reduce to the
identity in `A8 *_H A8`, while the hard class-11 pair reduces into `H`.
Consequently the aligned spherical module sees no nontrivial holonomy to
project.  See `FALSE_CLASSICAL_SPHERICAL_RAW_PACKET_COLLAPSE.md`.

Together with `TRUE_ATLAS_NONINCIDENT_FLAG_TYPE_REDUCTION.md`, `(RCS1)` made
the now-completed bounded audit literal:

1. represent both `A8` factors on a regular chart;
2. form the right-`H` nonincident-flag spherical module;
3. evaluate the 25- and 175-syllable words there; and
4. project their closed holonomies first to the multiplicity-one 35 and 56
   constituents, then, only if necessary, to the repeated 14 doublet.

The hard class-11 prefix and next-letter words are already explicit in
`experiments/atlas-boundary-11-30.json`.  Thus every group element in the
finite packet now has source coordinates.  The audit proves that the
coefficient two-child identities do not induce a nontrivial closed spherical
holonomy at the classical fold.  The live use of these words is instead in a
nonlinear block calculation on a Reynolds-misaligned two-chart microstate,
before fixed spherical projection.

## 4. Replay

The compiler and complete encoded words are

```text
experiments/atlas_raw_compressor_source_words.py
experiments/atlas-raw-compressor-source-words.json
```

Run on MSI with one core:

```text
module load python3/3.12.4_anaconda2024.06-1_libmamba
PYTHONPATH=experiments \
  python3 experiments/atlas_raw_compressor_source_words.py \
  > experiments/atlas-raw-compressor-source-words.json
```

The verifier reconstructs the two Leavitt targets independently, compiles
each elementary factor, evaluates the complete source words, and checks
exact equality by all-depth prefix expansion.  There are no numerical
tolerances.
