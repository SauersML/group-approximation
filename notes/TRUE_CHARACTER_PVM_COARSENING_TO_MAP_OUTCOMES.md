# Character PVMs coarsen canonically to whole-map outcomes

Date: 2026-08-13

## 1. Outcome

The whole-map PVM criterion does **not** require constructing one new
projection for every response map independently.  Suppose a finite additive
coefficient window has an atomic character PVM

```text
E : X -> Proj(M),      sum_x E_x=1,                    (CPC1)
```

and one character outcome `x` determines an entire response map through a
decoder

```text
decode : X -> Map(V,V).                               (CPC2)
```

Then put

```text
P_R = sum_(x:decode(x)=R) E_x.                        (CPC3)
```

The family `(P_R)` is automatically a PVM: different decoder fibers are
disjoint, their union is `X`, and sums of orthogonal projections are
projections.  If a second character PVM commutes with `(E_x)`, its analogous
map PVM commutes with `(P_R)`.  For a joint edge law

```text
q(x,y)=tau(E_x F_y),                                  (CPC4)
```

the induced map law is exactly its deterministic pushforward:

```text
mu(R,L)=sum_(decode(x)=R,decode'(y)=L) q(x,y).         (CPC5)
```

Thus normalization, positivity, commutation, and matching shared marginals
survive the coarsening without a dimension-dependent loss.

The finite scalar identities are formalized source-first in
`GroupApproximation/Leavitt/FiniteOutcomeCoarsening.lean`:

* `pushforwardWeight` and `pushforwardPairWeight`;
* nonnegativity of both constructions;
* exact preservation of total mass; and
* preservation of probability normalization.

They were not compiled in this iteration, following the explicit
no-compilation instruction.

## 2. What this removes from the live gate

The map space has cardinality `|V|^|V|`, so asking to round that many
unrelated approximate projections looked like a separate large-outcome
problem.  Equations `(CPC1)--(CPC3)` remove it.  A single joint character
measurement already packages all responses; map outcomes are only a
coarsening of its atoms.

Consequently the live operator target can be weakened from

```text
construct and round a PVM indexed directly by Map(V,V)
```

to

```text
extract one finite character PVM and one deterministic decoder whose
responses respect coefficient multiplication on the required window.
                                                               (CPC6)
```

This also gives matching map marginals for free whenever the two edge laws
use the same character PVM and the same decoder on their shared endpoint.
The tree-gluing theorem then produces the common law needed by the robust
`1/36` floor.

Nor must the decoder land in one fixed quotient rank.  Each character atom
may carry its own nonzero paired radical quotient.  The pointwise weighted
error floor is at least `1/4` for every such fiber, independently of its
dimension, and convex averaging preserves it.  Consequently no rank
pigeonhole or positive-density fixed-rank selection is part of `(CPC6)`.

## 3. The remaining word is multiplication-coherent

Additive exactification already supplies character PVMs on every fixed
finite root window.  It does **not** supply the decoder in `(CPC6)`.  The
finite-window automorphism-completion lemma in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md` gives exact atomic
models for all additive moments and injective corner covariance on any
fixed window.  Those models may choose arbitrary basis completions outside
the protected subspaces, so they do not respect the bilinear values

```text
b_ell(a,b)=ell(ab)                                    (CPC7)
```

under all four coefficient arrows.

The needed decoder must descend through the left and right radicals of
`(CPC7)` and satisfy, on one common finite label space,

```text
b(R_i a,L_j b)=delta_ij b(a,b).                       (CPC8)
```

The robust paired-quotient theorem says that `(CPC8)` has a fixed error
floor.  The local additive countermodel says `(CPC8)` cannot be inferred
before multiplication is used.  Hence the exact remaining extraction gate
is now:

> Recover a finite atomic character window for the two root charts on which
> the cross-root Steinberg commutators make the corner-pullback decoder
> multiplication-coherent, with total normalized-HS error tending to zero.

No direct exponential-outcome rounding theorem remains necessary after
that recovery.

## 4. Audit of the Clifford detour

A parallel check considered whether Clifford/CAR quantization made the
Kun--Thom orbit automatically Connes embeddable.  Existing repository audits
already isolate the coherent Bogoliubov-innerness obstruction and the sharp
fermionic `sqrt(d)` amplification loss.  The primary-source extension theorem
of Elek--Szabó has the direction

```text
sofic kernel + amenable quotient => sofic extension,
```

not “amenable kernel + sofic quotient.”  Therefore it cannot establish
soficity or hyperlinearity of the generalized Kun--Thom wreath product, and
the CAR detour does not bypass `(CPC6)`.
