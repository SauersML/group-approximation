# Compatible regular profiles for the full boundary packets

2026-09-08. The reconstructed six-coordinate packet and the full
boundary packet admit exact finite-dimensional representations agreeing
on their entire intersection and retaining the head. This gives a
specific obstruction to extracting a dimension-independent contradiction
from their finite-subgroup character or fixed-space data alone. It does
not construct a representation satisfying the remaining mixed relators.

## 1. The intersection of the two finite packets

Use the notation and faithful literal realizations from
[the opposite-root reconstruction](jacobson-full-boundary-opposite-roots-and-gl6-packet-2026-09-08.md):

```text
B=K x delta(G_P) ~= GL_6(F_2) x GL_3(F_2),
C=C_0 x C_far    ~= GL_5(F_2) x GL_3(F_2).
```

The local group `K` acts on all six coordinates of levels zero and
one. The subgroup `C_0` acts on the five of these coordinates other
than `e_(2,1)`. The farther factor `delta(G_P)` acts on the original
level triples at levels at least two. The factor `C_far` acts on
shifted triples `(e_(1,n),e_(2,n-1),e_(3,n))`, for `n>=2`.

Their exact intersection is

```text
Z=B intersect C=C_0 x delta(K_P)
  ~= GL_5(F_2) x GL_2(F_2).                           (1)
```

Indeed, a farther shifted matrix which preserves the original levels
cannot mix the second shifted coordinate with the first and third.
This can already be read on arbitrarily far triples, where neither
local factor acts. Over `F_2` its one-dimensional second block is the
identity, leaving exactly `K_P`. After removing this common farther
factor, an element in the intersection lies in the local `C_0`.
Conversely both factors in (1) are shared by construction. Since the
literal representations of `B` and `C` are individually faithful,
this calculation also proves the asserted abstract intersection.

## 2. Exact regular representations glue on that intersection

The finite group orders satisfy

```text
|GL_6(F_2)| / |GL_5(F_2)| = 2^5(2^6-1)=2016,
|GL_3(F_2)| / |GL_2(F_2)| = 28.
```

Put `d=|B|`. On dimension `d`, take the regular representation of
`B` and `2016` copies of the regular representation of `C`. Their
restrictions to `Z` are both

```text
56,448 copies of the regular representation of Z,     (2)
```

because restriction of the regular representation of a finite group
to a subgroup is its index times that subgroup's regular representation.
Choose a unitary intertwiner between these restrictions and conjugate
the second representation by it. The two finite packets now agree
exactly on `Z` in one matrix space.

Both representations are faithful. In particular the head involution
`w=x_13,Q` survives with `||w-I||=2`. Every nonidentity element in
either packet has character zero. Consequently the necessary trace
equalities among `h`, `b`, and `c` are satisfied: `h` belongs to
`C`, while `b,c` belong to `B`, and all three are nonidentity.
For every finite subgroup `A` of either packet, its averaging
projection has rank

```text
rank((1/|A|) sum_(a in A) pi(a))=d/|A|.              (3)
```

The same compatibility persists for finite-subgroup averaging on the
conjugation representation. Its character is
`chi_Ad(g)=|chi_pi(g)|^2`, so it restricts to `d^2/|B|` copies
of the regular representation of `B`, and respectively `d^2/|C|`
copies for `C`. In particular the corresponding fixed-space dimensions
are `d^2/|A|`. Passing to matrix commutants does not remove this
regular profile.

## 3. The precise limit of the obstruction

This construction proves feasibility for the two finite packets and
their full overlap. It does not assert that an intertwiner in (2) can
be chosen to solve `(hb)^3=1` and `W=1`. Those mixed operator
identities contain information beyond the listed character profiles.

There is also a general restriction on an exact projection strategy.
If `p` is a finite-support self-adjoint idempotent in `C[Gamma]` and
`v` is a finite-support unitary, a universal relation `vpv*<=p`
forces equality. In the left regular representation, the canonical
faithful finite trace vanishes on the positive difference; that
difference is therefore zero. The regular representation is injective
on `C[Gamma]`, so the original finite-support difference is zero as
well. Finite-subgroup averages, finite-packet spectral projections,
and finite polynomial expressions that are projections fall within
this argument.

This specializes the existing
`universal-relations-cannot-force-proper-infiniteness` barrier to exact
finite-support compression identities. It does not exclude
representation-dependent arguments or spectral projections outside
the group algebra. No almost-invariant-vector estimate for an infinite
subgroup is used or supplied here. The uniform mixed gap for the
full boundary presentation remains open.
