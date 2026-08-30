# STW LXVI: coherent CAR construction no-go audit (2026-08-30)

## Exact open construction boundary

The existing reductions turn Problem LXVI into constructing a simple unital
finite but non-stably-finite algebra containing CAR unitally.  The first
unstable matrix size is irrelevant.  A unital CAR corner is equivalent to a
coherent halving chain in the projection monoid, but neither divisibility in
`K_0` nor independently available finite matrix stages supplies that chain.

Known no-go results already exclude three natural shortcuts:

- tensoring a non-stably-finite finite seed by CAR;
- assembling independent dyadic stages in a simple norm ultraproduct; and
- making the CAR tail asymptotically central when the ambient double is
  infinite.

The finite-index obstruction below is independent of all three.  It assumes
that the coherent CAR copy is already present and instead controls the size
of its ambient module envelope.

## Finite Watatani-index obstruction

Let `D subset A` be unital, with `D` stably finite, and suppose a conditional
expectation `E:A->D` has a finite Watatani quasi-basis `u_1,...,u_r`.  The
quasi-basis identity makes `A`, with `D`-valued inner product
`<x,y>=E(x^*y)`, a finitely generated projective right Hilbert `D`-module.
The proof node avoids treating this as a black box: it writes the associated
corner representation explicitly as

```text
p_(ij)=E(u_i^*u_j),
rho(a)_(ij)=E(u_i^*a u_j),
rho:A->pM_r(D)p.
```

The quasi-basis equations show directly that `p` is a projection, `rho` is a
unital star homomorphism, and `rho` is faithful.  Stable finiteness of `D`
passes to matrix corners and unital subalgebras, so `A` is stably finite.

Taking `D` to be the embedded CAR algebra proves a new construction no-go:
an LXVI ambient algebra or either equivalent finite seed cannot carry a
finite-index expectation onto that CAR copy.  Its coherent dyadic tower must
have genuinely infinite module index in the ambient algebra.

This excludes finite-group crossed products of CAR, finite towers of
finite-index expected extensions, and injective limits assembled from such
stages.  The obstruction uses no trace extension, quasitrace, `K_0`, central
sequence, or simplicity argument.

## Infinite-index crossed and free constructions

There is a complementary obstruction which permits infinite Watatani index.
For any action of any discrete group on CAR, uniqueness makes the CAR trace
invariant.  Composing it with the faithful canonical expectation from the
reduced crossed product gives a faithful trace, so the crossed product is
stably finite.  If the full crossed product is simple, its canonical quotient
onto the reduced crossed product has zero kernel and the same conclusion
holds.

The identical vacuum mechanism applies to reduced amalgamated free products.
If `D=CAR subset A_i`, the expectations `E_i:A_i->D` are faithful, and
`tau_D after E_i` is tracial on every leg, then the reduced free-product
expectation `E` is faithful and `tau_D after E` is a faithful trace.  Scalar
amalgamation gives the ordinary reduced free product of CAR with any family
of faithfully tracial factors.  A simple full amalgamated or ordinary free
product coincides with its reduced quotient and is likewise stably finite.

This excludes arbitrary-group reduced crossed products, trace-preserving
reduced free amalgams, and their simple full counterparts.  Unlike the
finite-index theorem, it does not compress the ambient algebra into a fixed
matrix corner and places no bound on module index.  It instead shows that
the coherent dyadic tower carries its unique trace through every
trace-preserving reduced-word construction, preventing matrix instability.
Faithful traces remain faithful on matrix and hereditary corners, so cutting
to a full or simple corner cannot repair the construction.  The existing
injective-limit theorem similarly excludes injective limits of such corners.

## Z-stable projection dichotomy

There is an independent ambient-regularity obstruction.  Rordam's almost
unperforation theorem for Z-stable algebras, combined with the elementary
fact that an infinite projection in a simple algebra is properly infinite,
gives the dichotomy

```text
simple + unital + Z-stable
    => stably finite, or every nonzero projection properly infinite.
```

The direct comparison proof is useful here.  If the unit is properly
infinite and `p` is nonzero, finite, and hence full, compact fullness gives
`n[p]=[1]` for some `n`.  Almost unperforation applied to

```text
(n+1)[1]=[1]=n[p]
```

forces `[1]<=[p]`, so `p` is equivalent to the properly infinite unit, a
contradiction.  If instead the unit is finite, applying this mixed-projection
exclusion inside every matrix amplification shows that all amplifications
are finite.

Therefore no LXVI ambient algebra is Z-stable.  Winter's implication from
finite nuclear dimension to Z-stability for separable simple unital
non-elementary algebras then shows that every separable LXVI witness must
have infinite nuclear dimension.  This no-go makes no assumption about an
expectation onto CAR, module index, trace extension, `K_0`, central sequences,
or reduced-product assembly.

## Trust boundary

The theorem requires a finite Watatani quasi-basis, not merely a faithful
conditional expectation or a Pimsner--Popa lower bound.  Without a finite
quasi-basis the Hilbert-module completion need not be a finitely generated
projective module, and there is no fixed matrix corner `pM_r(D)p` into which
the ambient algebra must embed.  No obstruction is claimed for infinite-index
expected CAR inclusions.

The finite-index mechanism also does not obstruct a nonexpected, highly
noncentral CAR inclusion.  Such infinite-index inclusions remain the live
coherence frontier after the existing tensor, reduced-product, ultraproduct,
and central-matrix no-go results.  The Z-stable dichotomy further requires a
successful ambient algebra to be non-Z-stable (and, in the separable case,
of infinite nuclear dimension); it gives no contradiction for an irregular
infinite-index noncentral construction of that kind.

The free-construction theorem requires faithful trace-preserving
expectations on the legs (or an action by automorphisms in the crossed-product
case).  A faithful expectation onto CAR need not make `tau_D after E`
tracial, and a nonsimple full product may have a nonzero regular kernel, so
neither is claimed.  Those non-trace-preserving, nonreduced possibilities
remain outside this obstruction.
