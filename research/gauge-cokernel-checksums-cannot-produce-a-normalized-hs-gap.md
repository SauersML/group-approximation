---
rg: 2
id: gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap
kind: claim
title: A checksum on the cokernel of local repair directions can classify but never quantify
distinct_from:
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that treats congruence and divisibility refinements of one fixed A4 multiplicity polytope; this treats an arbitrary integral quotient by a prescribed matrix of locally realizable repair directions and separates the diagnostic use of that quotient from the completion use.
  finite-rational-rank-flows-are-fd-dense: that proves rational stationary flows are approximable by finite-dimensional ones; this draws the methodological consequence for the design pattern of first quotienting local gauge and then reading a Smith-normal-form invariant.
  finite-orbital-checksum-cannot-expose-sl3-coset-module: that computes one specific orbital checksum on the SL3 coset module and shows it is blind to the module; this is the general statement for every integral cokernel functional built from fixed finite packet rank data.
  atlas-fixed-rank-arithmetic-cannot-authenticate-s3-incidence: that rules out fixed rank arithmetic as an authenticator of one incidence pattern; this rules out the quotient-then-Smith-form design pattern as a source of any dimension-free normalized-HS lower bound.
---

**ESTABLISHED NO-GO.**  Consider the following design pattern, which is the
natural transfer of the "quotient the local gauge, then read the residual
integer" calculus into this program.  Fix a finite packet and let

```text
m=(m_1,...,m_N) in Z^N                                  (GCC1)
```

collect its retained rational rank/multiplicity coordinates.  Let

```text
D=[d_1 ... d_r],   d_j in Z^N                           (GCC2)
```

be the integral matrix whose columns are the locally realizable repair
directions (the modifications that the local tables already permit), and put

```text
Q=Z^N/im(D),   gamma:Q->Z or Q->F                       (GCC3)
```

for a proposed residual checksum.  The pattern proposes to distinguish a
distinguished source model `m_src` from an unwanted witness `m_wit` by
`gamma(m_src)=0`, `gamma(m_wit)!=0`, and then to promote that separation into
a positive normalized-HS lower bound.

The promotion step is impossible.  Split `gamma` through the structure of `Q`.

1. **Torsion part.**  If `gamma` takes values in a finite abelian group `F` of
   exponent `e`, then by `atlas-fixed-packet-arithmetic-has-no-hs-gap` the
   amplification `m |-> e m` lies in `ker(gamma)` while leaving the normalized
   profile `m/dimension(m)` unchanged.  A normalized-HS cost is a function of
   the normalized profile, so `gamma` and the cost cannot be comparable:
   `gamma` is destroyed by an operation that fixes every normalized quantity.

2. **Free part.**  If `gamma` is a primitive `Z`-valued linear functional,
   then `gamma(m)/dimension(m)` is a continuous degree-zero function on the
   normalized profile simplex.  By `(APA2)` the closure of realizable
   normalized profiles is the full convex hull of the atomic type vectors, and
   by `(RFD2)` every rational point of that hull is realized after clearing a
   denominator.  Hence, whenever an exact tracial model of the local data
   exists at all, matrix profiles accumulate on its normalized profile and

   ```text
   inf { |gamma(m)|/dimension(m) : m a matrix profile } = 0.   (GCC4)
   ```

   Direct sum with amplified copies of the source realizes `(GCC4)`
   explicitly: `gamma(m_wit + k m_src)=gamma(m_wit)` is fixed while the
   normalized value tends to zero.

3. **Mixed.**  A general `gamma` is a finite sum of the two cases and inherits
   both failures.

Therefore no invariant of `(GCC3)` — no Smith normal form of `D`, no primitive
low-support detector on `coker(D)`, no congruence residue — can supply a
dimension-free positive lower bound for a normalized-HS defect.  This holds
however cleverly the local repair directions were quotiented first; the
quotient does not change which data the checksum is a function of.

## What the pattern is still good for

The computation remains a legitimate **no-go generator**, and a cheap one.
If, for a proposed moment vocabulary,

```text
coker(D)=0,   or   m_src = m_wit in coker(D),           (GCC5)
```

then that vocabulary provably cannot separate the source from the witness at
all, and the separation half of the programme is dead before any estimate is
attempted.  This is the correct use: run the Smith form to *refute* a
vocabulary, never to *complete* a route.

## Scope

The statement is about functionals of the fixed finite packet's rational rank
data.  It says nothing about invariants that also read multiplicity
intertwiners, cycle holonomy, projective cocycles, or analytic Gram
coordinates; `(RFD3)` names exactly the extra hypotheses under which the
finite-dimensional density argument stops.  Those are the invariants that can
still carry a gap, and they are not computed by a Smith normal form.
