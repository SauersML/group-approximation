---
rg: 2
id: fixed-packet-spectral-correction-is-gap-or-regular-collapse
kind: claim
title: Fixed-packet spectral correction needs new coercivity or becomes regular-factor functorial
distinct_from:
  fixed-packet-julia-calculus-is-tracially-functorial: that treats continuous Halmos and Julia calculus on one packet corner; this adds hard spectral cuts and fixed finite-dimensional polynomial identities, the two proposed matrix-only escapes after the Halmos firewall.
  fixed-rank-index-authenticator-has-gap-or-functoriality: that treats rank, kernel, index, and determinant readouts of one rectangular operator; this applies the dichotomy to a pair of corrected proper-corner projections and includes the marked-exit consequence.
  universal-block-return-violates-the-regular-firewall: that proves collapse once conjugacy and containment are tracially functorial; this proves a fixed finite packet plus uniformly stable spectral correction cannot keep those relations matrix-only.
---

Fix a finite packet group `F` and one irreducible type `rho` of dimension
`r`.  After exactification, its matrix carrier is

```text
C^r tensor C^m,                                        (FSC1)
```

where the multiplicity `m` is arbitrary and unbounded.  Consider a fixed
decoder which, from packet matrix units and finitely many bounded corrected
word operators, constructs projections `Q_m,R_m` and a unitary `W_m` using:

- fixed star-polynomials and fixed matrix amplifications;
- polar correction on a uniformly invertible Gram operator; and
- finitely many spectral cuts at fixed thresholds.

Suppose the decoder is intended to have a dimension-independent normalized-HS
modulus and prove

```text
||R_m-W_m Q_m W_m^*||_2+||R_m-R_m Q_m||_2
 <= omega(def),             omega(t)->0.                (FSC2)
```

Then the finite packet and the listed calculus do not by themselves make the
decoder a finite-matrix-only proper-corner actuator.  Either a new spectral
coercivity theorem supplies the modulus, or the construction is functorial
and hits the regular-factor firewall below.

## Spectral-cut dichotomy

For a hard cut at `theta`, the exact normalized-HS continuity datum is a
uniform spectral-mass modulus

```text
sup tau(1_[theta-eta,theta+eta](H)) <= kappa(eta),
kappa(eta)->0.                                           (FSC2a)
```

Without `(FSC2a)`, a positive-density multiplicity summand may remain
arbitrarily close to the threshold.  Moving the operator by `2 eta` on that
summand changes its HS norm by at most `2 eta` while changing the cut by the
square root of that density.  Hence the **finite packet alone** supplies no
dimension-independent cut modulus.  Relations excluding these perturbations
must prove the additional spectral-coercivity statement `(FSC2a)`.

If the stronger uniform empty-band condition holds, choose one continuous
function which equals the indicator on all allowed spectra.  More generally,
`(FSC2a)` plus the usual `eta`-window decomposition gives a uniform L2
approximation of the hard cut by continuous functions: for a continuous ramp
`f_eta` which differs from the indicator only in the displayed window,

```text
||1_[theta,infinity)(H)-f_eta(H)||_2^2 <= kappa(eta).   (FSC2b)
```

Approximate `f_eta` uniformly by one polynomial; telescoping that fixed
polynomial transfers HS perturbations with a dimension-free constant.  Thus
any cut whose
stability is proved by a tracially functorial mass estimate belongs to the
same finite-von-Neumann calculus.  Polar correction under a uniform Gram
bound is continuous as well.
Consequently the whole decoder is defined verbatim after replacing the
matrix multiplicity algebra `M_m(C)` by an arbitrary finite tracial von
Neumann algebra `N`:

```text
M_r(C) tensor M_m(C)   ->   M_r(C) tensor N.            (FSC3)
```

All normalized-HS estimates are unchanged.  Evaluating `(FSC2)` at zero
defect in the canonical regular finite factor gives

```text
R=WQW^*,                         R=RQ.                  (FSC4)
```

Trace cyclicity and faithfulness force `R=Q`.  Therefore the corrected exit
`Q(1-R)Q` vanishes in the regular representation.  If the same fixed decoder
also authenticates the negative spectral carrier of a marked involution
below that exit, the left regular representation sends the involution to the
identity; faithfulness on group elements makes the mark trivial in the group.
Thus an exact properly infinite marked model cannot rescue this functorial
decoder.

## Fixed polynomial identities do not provide another case

A fixed noncommutative polynomial which vanishes on the multiplicity factor
`M_m(C)` for every unbounded `m` is the zero polynomial identity.  Indeed, for
a polynomial of word degree `d`, the truncated left shifts on the finite set
of words of length at most `d` isolate every word coefficient.  Hence a
nonzero fixed polynomial fails in some finite multiplicity dimension.

The same conclusion holds for a fixed finite family of polynomial identities
or fixed-degree standard identities.  An Amitsur--Levitzki identity can see a
specified matrix size only by increasing its degree with that size; one fixed
presentation cell cannot use it for the arbitrary `m` in `(FSC1)`.  If packet
relations force the fixed polynomial to vanish for every multiplicity, the
identity is again algebraic and valid in `(FSC3)`, so it returns to the
regular-factor case above.

Therefore a successful matrix-only proper-corner decoder must use data not
contained in one fixed corrected packet: a spectral-mass/coercivity estimate
which itself fails in the regular factor, a dimension-dependent/growing
polynomial family, an extensive coercive syndrome system, or a nonfunctorial
global finite-coordinate choice.  Merely taking a canonical fixed spectral
projection or invoking a fixed polynomial identity cannot supply the
surviving localization gate.
