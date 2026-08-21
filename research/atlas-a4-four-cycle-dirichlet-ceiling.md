---
rg: 2
id: atlas-a4-four-cycle-dirichlet-ceiling
kind: claim
title: The exact A4 network keeps the minimal four-cycle Dirichlet energy below one over 1536
distinct_from:
  atlas-a4-four-cycle-dirichlet-compiler: that stronger target makes the four-cycle energy vanish at a rate controlled by packet and collision defect; this target asks only for one fixed numerical ceiling along the normalized necessity sequence.
  atlas-a4-holonomy-coherence-gap: that target bounds the two raw S3 covariance directions; this target bounds the four minimal A8 cycle directions before the exact finite transfer to the raw S3 detector.
---

For a normalized exact-regular A4 context-network sequence, put

```text
E_n = sum_(t in {t01,t12,t23,t30})
        (1-Re tau_n(V_n(t))).
```

Prove the strictly weaker numerical statement

```text
limsup_n E_n < 1/1536.                                  (A4-DIR-CEIL)
```

No modulus tending to zero is required.  The constant is chosen so that the
exact transfer `atlas-a8-four-cycle-controls-raw-s3-energy` gives

```text
limsup_n (a_n^2+b_n^2)
 <= 48 limsup_n E_n
 < 48/1536
 = 1/32,
```

which is already the complete holonomy-coherence gap needed by the direct
nonhyperlinear route.

Thus the new highest-level analytic target is a **finite constant-gap energy
ceiling**, not synchronization, reconstruction, or asymptotic chart-frame
collapse.

## Attempts

- **Search a finite constant-gap SOS, not a vanishing estimate.**  A cyclic
  sum-of-squares certificate only has to leave slack `1/1536`; it need not
  dominate the four-cycle energy by the small residual norm with a uniform
  Lipschitz modulus.
- **Optimize the constant before the proof.**  The current `24` transfer comes
  from one exact eight-letter word for `t21`.  Any lower weighted word-energy
  certificate, or direct finite-group Dirichlet comparison from the four-cycle
  to `{t21,t12}`, enlarges the admissible ceiling automatically.
- **Use tracial compactness qualitatively.**  It is enough to rule out limiting
  exact A4/collision models carrying four-cycle energy at least `1/1536`.
  Quantitative stability of every intermediate gauge is unnecessary.
- **Dual-search bad multiplicity modes.**  If the ceiling fails in a finite
  truncation, keep the maximizing tracial/multiplicity mode as a concrete dual
  obstruction and enlarge only the packet residuals that see it.
- **Audit the abstract packet-collision quotient first.**
  `atlas-a4-packet-collision-quotient-audit` gives the formal finite fork, but
  `atlas-charts-overlap-trivially` removes its favorable branch: true kernel
  relators cannot collapse either chart factor.  Therefore finiteness would
  return an exact regular-margin countermodel, not prove this ceiling.

## Quotient trace fork

Let

```text
Gamma_A4=(A8*A8)/<<thirty packet words,q_19243>>.
```

All thirty-one relators lie in the kernel of the canonical two-chart map to
`Q=L_(F2)(1,2)^x`.  By `atlas-charts-overlap-trivially`, both chart factors
are faithful and have trivial intersection in `Q`.  Since the map factors
through `Gamma_A4`, the two `A8` factors are also injective and disjoint in
`Gamma_A4`.  In particular the collapsed-factor branch of
`atlas-a4-packet-collision-quotient-audit` cannot occur.

This makes every standard positive permanence result point in the wrong
direction for `(A4-DIR-CEIL)`:

1. If `Gamma_A4` is finite, its regular representation is an exact
   finite-dimensional packet-plus-collision model with both chart margins
   regular.
2. If `Gamma_A4` is residually finite or sofic, it is hyperlinear, so its
   canonical trace supplies asymptotic matrix models with the same regular
   margins.
3. More generally, if the canonical trace of `Gamma_A4` is Connes-embeddable,
   finite-dimensional matrix microstates supply the same sequence after
   finite-group exactification of the two chart restrictions.

In each case align the first chart and absorb the second alignment into one
relative unitary `U_n`.  For `t in T`, disjointness of the chart factors gives

```text
i_2(t)i_1(t)^-1 !=1.
```

The canonical regular character therefore gives

```text
Re tau(V_n(t))->0,
E_n->4.                                                (A4-QUOT-ESCAPE)
```

Thus any of the three properties above refutes the claimed ceiling by a wide
margin.  In particular a successful finite quotient computation cannot close
the A4 lane; it closes the countermodel branch.

There is also a conditional countermodel directly from the intended Leavitt
target.  If `Q` were hyperlinear, pull its canonical matrix microstates back
along `Gamma_A4->Q`.  The chart restrictions are regular because both `A8`
factors embed in `Q`, and their cross-elements remain nonidentity because the
charts intersect trivially.  After the standard exact-regular normalization,
this again gives `(A4-QUOT-ESCAPE)`.  Proving the ceiling is therefore already
a proof that this pulled-back trace is not Connes-embeddable.

## What existing obstructions do not decide

- The 15-point classical audit and the 31-point `GL5(F2)` screen exclude only
  two fixed finite representation families.  They do not separate the
  canonical quotient trace from all matrix traces.
- The `1/32` collision-to-commutant wall is consistent with, rather than an
  obstruction to, the quotient trace: the quotient frame is noncentral and
  its four-cycle energy is maximal.
- Ordinary normal-closure and cyclic tracial SOS arguments cannot work.
  `atlas-charts-overlap-trivially` prevents algebraic chart collapse, and the
  finite-factor model recorded in `atlas-a4-four-cycle-dirichlet-compiler`
  satisfies all exact relations with `E_T=4`.
- `Gamma_A4` is a quotient of the sofic group `A8*A8`, but hyperlinearity does
  not pass to arbitrary quotients by any available theorem.
  `hyperlinear-quotient-permanence-equivalence` identifies such unrestricted
  permanence with the whole existence problem for nonhyperlinear groups, so
  it cannot be invoked here as a routine closure property.

No existing finite-dimensional obstruction in the A4 lane proves the
canonical quotient trace non-Connes-embeddable, and no established permanence
property proves `Gamma_A4` hyperlinear.  The decisive fork is therefore
unresolved.  The exact remaining theorem is matrix-specific trace exclusion
for `Gamma_A4` (or for the pulled-back canonical trace of `Q`), not quotient
finiteness and not a universal tracial inequality.

Accordingly this claim remains open.
