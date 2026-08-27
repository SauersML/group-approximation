---
rg: 2
id: finite-normalizer-star-no-go
kind: claim
title: Finite packet normalizers retain a Plancherel model and cannot authenticate a marked binary swap star
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs compatible regular type vectors for arbitrary finite graphs of finite groups; this gives the one-vertex conditional-trace obstruction specific to the marked binary swap star and includes automorphism/self-similarity normalizers.
  cyclic-conjugacy-does-not-synchronize-swap-sources: that transports coordinate projections around a finite graph; this shows that even an asserted common marked source cannot be universally authenticated inside one finite packet.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that realizes arbitrary finite binary clone patterns in locally finite affine groups; this isolates the smaller Plancherel obstruction faced by any actuator which merely normalizes a fixed star packet.
---

Let `K` be finite, let `y` be a nonidentity central involution of `K`, and
let `j_0,j_1` be involutions.  Put

```text
p=(1-lambda_K(y))/2,              h=j_0j_1,           (FNA1)
```

in the left regular representation.  With `tau_K` normalized, the marked
conditional moment is exactly

```text
tau_K(ph)/tau_K(p)=delta_(h,1)-delta_(h,y).            (FNA2)
```

Indeed `tau_K(p)=1/2` and

```text
tau_K(ph)=1/2(tau_K(h)-tau_K(yh)).                    (FNA3)
```

Suppose the restrictions of `j_0,j_1` to `p l2(K)` were a nonzero binary
common-source orthogonal-range swap star.  The marked star theorem would
make the left side of `(FNA2)` at least `1/4`.  Formula `(FNA2)` then forces
`h=1`.  Since the `j_i` are involutions, `j_0=j_1`; equality of the two swap
matrices makes their range projections equal, and orthogonality forces the
common source to be zero.  Contradiction.

Therefore no finite packet, however large, can make its whole marked
Plancherel sector into a nonzero binary swap star.  This remains true even
though one selected irreducible type of that packet may realize the desired
geometry exactly.

## Automorphism actuators preserve the countermodel

Let a group `A` act on `K` through automorphisms.  The semidirect product

```text
K rtimes A                                               (FNA4)
```

has an exact finite-dimensional representation on `l2(K)`: `K` acts by its
left regular representation and `a in A` acts by the permutation

```text
delta_k -> delta_(a.k).                                (FNA5)
```

Only the finite image of `A -> Aut(K)` is visible.  Thus adjoining stable
letters, Thompson-style renamings, a finite cycle, or an expander which acts
only by automorphisms of the fixed packet cannot remove `(FNA2)`.  Common
amplification gives the same zero-defect model in every larger dimension.

There is a packet-local energy version of the obstruction.  For a split
semidirect product `G=K rtimes H`, let `A` be the finite image of
`H->Aut(K)`.  The homomorphism

```text
G -> K rtimes A,                 (k,h) |-> (k,alpha_h)    (FNA6)
```

is a finite quotient and is injective on `K`.  Hence for every positive
`a in C[K]` its quotient-regular normalized trace agrees with the canonical
group trace:

```text
tr_(K rtimes A)(a)=tau_G(a).                             (FNA7)
```

Thus every trace-polynomial energy supported in the fixed packet satisfies
`beta_fd>=E_reg`.  A split finite packet/automorphism normalizer cannot be
the bounded energetic decoder in the cyclic reverse-Kleene route: it destroys
the required strict regular-versus-finite ceiling before any stability issue
arises.  A finite-packet candidate must at minimum use a nonsplit extension
or matrix-only holonomy on the multiplicity space.

The same argument applies to a finite orbit of packet copies: the regular
representation of the corresponding finite wreath/semidirect packet is a
stationary exact model.  For unbounded prefix clones,
`affine-clone-model-defeats-pure-thompson-prefix-error-spreading` supplies
the compatible locally finite version.

## Consequence for recursive error spreading

A viable self-similar star compiler must contain a relation absent from every
automorphism normalizer model.  Concretely it must do at least one of:

1. implement a genuinely proper/non-surjective corner correspondence;
2. impose a mixed two-dimensional holonomy or collision which fails on the
   regular packet; or
3. prove a matrix-only selected-carrier return from an infinite actuator.

Merely copying, permuting, conjugating, or expanding a fixed finite star
packet cannot authenticate the common-source chart.

## Attempts and firewalls

- **Select only `y=-1`.**  Formula `(FNA2)` is already conditional on that
  entire marked sector.
- **Add more packet automorphisms.**  They are all implemented by the finite
  permutation representation `(FNA5)`.
- **Use a selected finite irreducible.**  It may contain the star, but the
  regular marked sector contains the complementary types.  An additional
  source-saturation theorem is still required.
- **Claim all infinite actuators fail.**  The result does not say that.
  Proper-corner and contextual matrix-only actuators deliberately fall
  outside the automorphism hypothesis.
