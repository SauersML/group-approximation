# The raw source word gives a sharp direct Reynolds gap

Date: 2026-08-13

## 1. Outcome

Let `rho` be a regular multiple of the first `A8` chart and, after the
certified classical alignment, write the second chart as

\[
 g\longmapsto U\rho(g)U^*.
 \tag{RWG1}
\]

Put

\[
 \Delta_H=\max_{h\in H}\|U\rho(h)-\rho(h)U\|_2.
 \tag{RWG2}
\]

The compiled 25-syllable raw swap has exactly twelve second-chart letters.
Every one of those twelve letters lies in `H`.  If they are replaced by
their first-chart copies, the complete word reduces exactly to the identity.
It follows directly that

\[
 \boxed{\|r_{\rm src}(U)-1\|_2\le 12\Delta_H.}
 \tag{RWG3}
\]

The scalarized Leavitt image of `r_src` is the nonidentity raw swap `r`, so
`r_src` is nontrivial in the atlas group.  In a trace-preserving hyperlinear
model its normalized trace converges to zero, and hence

\[
 \|r_{\rm src}(U)-1\|_2\longrightarrow\sqrt2.
 \tag{RWG4}
\]

Combining `(RWG3)` and `(RWG4)` gives the new uniform bound

\[
 \boxed{\Delta_H\ge {\sqrt2\over12}-o(1).}
 \tag{RWG5}
\]

This replaces the previous lower bound obtained by transporting one root
through a length-19 bridge and then using a diameter bound as large as
`20159`.  The new constant comes from the raw packet itself and has no group
diameter loss.

There is a sharper form.  The twelve second-chart letters consist of only
two distinct elements `h_a,h_b in H`, occurring eight and four times.  Put

\[
 a=\|U\rho(h_a)-\rho(h_a)U\|_2,
 \qquad
 b=\|U\rho(h_b)-\rho(h_b)U\|_2.
 \tag{RWG5a}
\]

The same telescope gives

\[
 \sqrt2-o(1)\le8a+4b.
 \tag{RWG5b}
\]

Since

\[
 (8a+4b)^2\le80(a^2+b^2),
\]

we obtain the localized energy floor

\[
 \boxed{a^2+b^2\ge {1\over40}-o(1).}
 \tag{RWG5c}
\]

## 2. Telescoping proof

Write the transported raw word as

\[
 a_0\,h_1^{(2)}\,a_1\,h_2^{(2)}\cdots
 h_{12}^{(2)}a_{12},
 \qquad a_i\in G_1,\quad h_i\in H,
 \tag{RWG6}
\]

where `h_i^(2)` means evaluation in the second chart.  Exact amalgam
reduction certifies

\[
 a_0h_1a_1h_2\cdots h_{12}a_{12}=1
 \quad\text{in }G_1.
 \tag{RWG7}
\]

At matrix level, replace the twelve factors

\[
 U\rho(h_i)U^*\quad\text{by}\quad\rho(h_i)
\]

one at a time.  All prefix and suffix products are unitary, so normalized
Hilbert--Schmidt norm is unchanged by them.  Each replacement costs

\[
 \|U\rho(h_i)U^*-\rho(h_i)\|_2
 =\|U\rho(h_i)-\rho(h_i)U\|_2\le\Delta_H.
\]

The triangle inequality gives `(RWG3)`, and `(RWG7)` identifies the final
word with `1`.

No approximate group multiplication is hidden here after the two finite
chart factors have been exactified.  If the source microstate has a residual
word-evaluation error `epsilon_raw`, the same proof gives

\[
 \sqrt2-o(1)\le \epsilon_{\rm raw}+12\Delta_H.
 \tag{RWG8}
\]

## 3. Reynolds consequence

For the finite Reynolds projection

\[
 E_H(U)={1\over168}\sum_{h\in H}\rho(h)U\rho(h)^*,
\]

the exact mean-displacement identity is

\[
 {1\over168}\sum_{h\in H}
 \|U\rho(h)-\rho(h)U\|_2^2
 =2\bigl(1-\|E_H(U)\|_2^2\bigr).
 \tag{RWG9}
\]

The two named summands from `(RWG5a)` both occur in the full Reynolds sum.
Therefore `(RWG5c)` yields the sharper estimate

\[
 \boxed{
 1-\|E_H(U)\|_2^2
 \ge {a^2+b^2\over336}
 \ge {1\over13440}-o(1).}
 \tag{RWG10}
\]

Thus every hypothetical hyperlinear atlas sequence lies not merely outside
the aligned fold, but outside an explicit fixed Reynolds tube around it.

The two letters `h_a,h_b` are involutions and their product has order three.
Exact closure inside `H` has order six, so

\[
 K=\langle h_a,h_b\rangle\cong GL_2(2)\cong S_3.
 \tag{RWG10a}
\]

Let `E_K` be the six-term Reynolds projection.  Its mean-displacement
identity contains the same two nonnegative summands `a^2,b^2`, and therefore

\[
 \boxed{
 1-\|E_K(U)\|_2^2
 \ge {a^2+b^2\over 2|K|}
 \ge {1\over480}-o(1).}
 \tag{RWG10b}
\]

This is the strongest useful localization: the compulsory transverse energy
already occurs on an `S_3` slice, whose complex representation theory has
only the trivial, sign, and two-dimensional standard types.

The four first-chart letters form a second `S3` which centralizes this one;
the raw word is therefore confined exactly to an `S3*S3` transport cell.
The hard class-11 pair expands the common `S3` through two order-24 `S4`
subgroups which together generate `H=GL3(2)`.  See
`TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md`.

## 4. What this changes

The exact classical collapse of the raw word is not sterile: it makes the
word a pure detector of transverse `H`-covariance.  The useful information is
not a scalar spherical phase at the fold, but the quantitative amount of
misalignment required for the nontrivial raw word to survive.

The remaining obstruction is now localized to the compact annular regime

\[
 \|E_H(U)\|_2^2\le1-{1\over13440}+o(1).
 \tag{RWG11}
\]

A valid nonlinear block argument may assume this explicit deficit from the
start.  In particular, perturbative searches near `E_H(U)=U` are not merely
unsuccessful; they are disjoint from every hypothetical zero-defect
hyperlinear sequence.

More sharply, the first block calculation should now be performed over the
three-vertex `S_3` multiplicity quiver and may assume
`||E_K(U)||_2^2 <= 1-1/480+o(1)`.  Only if the comb and hard-pair relations
lose the necessary child labels under this smaller restriction should one
return to the full 168-element `H` quiver.

This still does not prove nonhyperlinearity.  A second inequality is needed:
the comb/interior relations must force Reynolds saturation or extract the
finite two-child coefficient arrows throughout the annular regime.  The
advance is that the lower side of the dichotomy is now short, exact, and has
a usable constant.

## 5. Replay

The exact word-structure audit is

```text
experiments/atlas_raw_reynolds_gap_audit.py
```

with committed output

```text
experiments/atlas-raw-reynolds-gap-audit.json
```

Replay on MSI with one core:

```text
module load python3/3.12.4_anaconda2024.06-1_libmamba
PYTHONPATH=experiments \
  python3 experiments/atlas_raw_reynolds_gap_audit.py \
  > experiments/atlas-raw-reynolds-gap-audit.json
```
