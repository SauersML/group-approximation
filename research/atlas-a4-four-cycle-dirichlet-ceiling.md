---
rg: 2
id: atlas-a4-four-cycle-dirichlet-ceiling
kind: claim
title: The exact A4 network keeps the minimal four-cycle Dirichlet energy below one over 1536
refuted_by: atlas-m2-escape-kills-collision-only-scalars
distinct_from:
  atlas-a4-four-cycle-dirichlet-compiler: that stronger target makes the four-cycle energy vanish at a rate controlled by packet and collision defect; this target asks only for one fixed numerical ceiling along the normalized necessity sequence.
  atlas-a4-holonomy-coherence-gap: that target bounds the two raw S3 covariance directions; this target bounds the four minimal A8 cycle directions before the exact finite transfer to the raw S3 detector.
---

**Refuted.**  The constant sequence given by the exact multiplicity-two
regular witness has packet and collision defect zero and four-cycle energy at
least one because its `t23` opcode has regular trace zero.

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

## Fixed rank and dimension checks do not separate the trace

The exact-regular normalization already absorbs every divisibility condition
coming from the finite chart and context groups.  The matrix dimension is

```text
d=|A8| k=20160 k.
```

For every subgroup `H<=A8`, restriction of the chart representation is

```text
k [A8:H] Reg(H).
```

Hence, for any spectral/idempotent block `p` in the finite group algebra of
`H`,

```text
rank(p)=k [A8:H] rank_(Reg(H))(p),
tr_d(p)=rank_(Reg(H))(p)/|H|.                          (A4-RANK-LOCAL)
```

All denominators from the `A8`, `A4`, `C3`, and `C2` cells therefore divide
`20160` and are integral in every allowed dimension.  The two chart copies
have identical rank vectors, conjugation by the common `U` preserves them,
and the collision equation is a multiplicative unitary equation which adds no
projection-rank balance.  Thus the local finite-group type ledger contains no
rank mismatch to exploit.

There are only two ways a fixed matrix-rank checksum could differ from its
finite-factor analogue, and both fail here.

1. A normalized rank equality or inequality derived from the exact relations
   passes to Murray--von Neumann dimension in finite tracial algebras.  The
   exact finite-factor common-`U` model with `E_T=4` from
   `atlas-a4-four-cycle-dirichlet-compiler` would satisfy it, so it cannot
   force the desired ceiling.
2. A purely integral congruence on finitely many ranks is destroyed by allowed
   amplification: replacing a matrix model by the direct sum of `m` copies
   multiplies every rank by `m` while preserving all normalized traces,
   relation defects, and `E_T`.  Choosing `m` divisible by the fixed moduli
   clears every such congruence.

Determinants give no extra checksum.  The determinant of the regular `A8`
representation is a one-dimensional character of the perfect group `A8`,
hence is identically one.  The same holds on every amplification and on the
conjugate second chart, so every packet and collision determinant identity is
automatic.

Finally, the map `Gamma_A4->L_(F2)(1,2)^x` is only a homomorphism into the
**unit group**.  A matrix representation of `Gamma_A4` need not extend to a
ring representation of the Leavitt algebra.  Therefore the additive Leavitt
relation and its impossible finite-dimensional rank equation cannot be pulled
back through this map.  Doing so would require a coefficient/ring decoder of
the kind separately asked for by
`affine-leavitt-steinberg-hs-coefficient-decoder`; none is present in the
thirty-one group words.

## The finite-coefficient pullback already fails on one order-three unit

There is an exact norm witness for the preceding coefficient obstruction.
Let `R=L_(F2)(1,2)` and let `g in R^x` be the order-three unit of
`leavitt-corner-idempotent-unital-surjection`.  In characteristic two it
satisfies

```text
1+g+g^2=0                 in R.                       (A4-COEFF-F2)
```

Choose any lift `h in Gamma_A4` under the canonical surjection
`Gamma_A4->R^x`.  The three group elements `1,h,h^2` are distinct: any
equality between them would make the image `g` have order at most two.  Hence
in the complex group von Neumann algebra of `Gamma_A4`, with canonical trace,

```text
Z=1+lambda(h)+lambda(h^2),
||Z||_2^2=3.                                             (A4-COEFF-C)
```

Indeed distinct group elements form an orthonormal basis of
`L^2(L(Gamma_A4),tau)`.  All thirty packet relators and `q_19243` are exactly
one in this representation.  Consequently no estimate of the form

```text
||1+H+H^2||_2 <= C max_j ||r_j(H)-1||_2
```

can be deduced from those relators, and no bounded coefficient-ideal
certificate can obtain `(A4-COEFF-F2)` by interpreting its `F_2` sum as a
complex matrix sum.  The failure is quantitative (`sqrt(3)`), occurs on a
three-term coefficient window, and survives every amplification.

This also explains why `leavitt-unit-group-algebra-surjects-onto-leavitt` and
the finite rank-three unit lifts do not provide the missing trace exclusion.
Their evaluation map is an `F_2`-algebra map, whereas Hilbert--Schmidt
microstates linearly generate a complex group algebra; there is no unital
coefficient map `F_2->C`, and the evaluation kernel is not trace-null after
changing coefficients.  The explicit atlas rank-five dictionary does not
repair this: it writes Steinberg generators as chart words, but the present
thirty-one-relator quotient does not impose the full additive/multiplicative
Steinberg coefficient table.

Thus a successful finite coefficient decoder cannot be a pullback of Leavitt
addition along the unit-group homomorphism.  It would have to construct new
matrix-only carrier projections and product operators from extra group-word
relations, as in the still-open
`affine-leavitt-steinberg-hs-coefficient-decoder`.  No such extra relations or
carrier authentication occur in `Gamma_A4`.  This is a sharp obstruction to
the proposed shortcut, not a proof that the quotient trace is Connes
embeddable or non-Connes-embeddable.

This rules out every fixed local rank, divisibility, and determinant checksum
available from the current quotient presentation.  It does not exclude a
genuinely matrix-specific obstruction with unbounded or microstate-dependent
index data.  No such invariant is currently compiled by the A4 packet.

Accordingly this claim remains open.
