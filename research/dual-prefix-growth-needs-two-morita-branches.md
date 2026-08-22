---
rg: 2
id: dual-prefix-growth-needs-two-morita-branches
kind: claim
title: Dual-prefix Pauli rank grows through two root-dependent Morita branches, not one automorphism
distinct_from:
  conjugate-local-signs-preserve-marked-carrier: that proves conjugate signs have equal spectral density; this determines exactly when the packet rank on those carriers can grow.
  leavitt-hnn-shift-has-sign-or-checksum-dichotomy: that classifies canonical ring endomorphisms of the elementary ambient; this constructs the stronger two-branch Heisenberg monomorphisms and identifies why they do not solve finite presentation.
  thompson-clifford-central-product-tape: that gives a finitely presented abstract Clifford central-product tape; this realizes the specific dual-prefix Leavitt coefficient maps but only on an infinitely generated root Heisenberg subgroup.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out changing one finite packet's multiplicity by one conjugacy; this separates rank-preserving single transport from rank-doubling commuting branch embeddings.
---

Let `B=ARA` be the active binary Leavitt corner.  Write `H(B)` for the
two-root Heisenberg group

```text
X(a)X(a')=X(a+a'),
Y(b)Y(b')=Y(b+b'),
Z(c)Z(c')=Z(c+c'),
[X(a),Y(b)]=Z(ab),                                    (DMB1)
```

with the `Z(c)` central and the same-species roots commuting.  For
`i=0,1`, define

```text
iota_i(X(a))=X(a t_i),
iota_i(Y(b))=Y(s_i b),
iota_i(Z(c))=Z(c).                                    (DMB2)
```

Then each `iota_i` is an injective group endomorphism of `H(B)`.  The two
images commute across their noncentral generators, because

```text
[X(a t_i),Y(s_j b)]=Z(a t_i s_j b)=1       (i!=j),     (DMB3)
```

and they share the entire center pointwise.  Iterating the two maps gives

```text
iota_u(X(A))=X(t_u),
iota_u(Y(A))=Y(s_u),                                   (DMB4)
```

up to the fixed prefix-order convention.  Hence the `2^n` images at depth
`n` are exactly the dual-prefix Heisenberg packet with common sign

```text
J=Z(A).                                                 (DMB5)
```

Thus rank growth is not forbidden by equal carrier rank or by allowing a
moving sign.  If another stable word `t` is used and the whole depth-`n`
packet is conjugated by `t^n`, its common center becomes

```text
J_n=t^n J t^(-n),                                      (DMB6)
```

and `conjugate-local-signs-preserve-marked-carrier` gives exactly equal
spectral traces for all `J_n`.  The packet on the `J_n` carrier still has
symplectic rank `2^n`.

The construction also pinpoints why an ordinary finite-presentation HNN
compiler has not been obtained.

1. `H(B)` is not finitely generated: modulo its center it surjects onto the
   additive group `B direct_sum B`, an infinite-dimensional `F_p`-vector
   space.  The standard two-letter multiple-HNN presentation implementing
   `(DMB2)` therefore has infinitely many edge relations.
2. The maps are root-dependent.  On the first root the coefficient map is
   right multiplication `a |-> at_i`; on the adjacent root it is left
   multiplication `b |->s_ib`.  No single ring endomorphism induces both:
   evaluating such an endomorphism at `A` would require its value to be both
   `t_i` and `s_i`, which are distinct homogeneous Leavitt elements.
3. A single automorphic or HNN transport sends a Pauli packet to an
   isomorphic packet and preserves its symplectic rank.  Growth occurs only
   because both branch images are present and commute as a central product.

Consequently the conjugate-sign idea clears the spectral-density issue.  On
the unstabilized Heisenberg subgroup it still leaves infinitely many HNN
edge relations, so a positive compiler needs a finitely generated ambient
which realizes both root-dependent branches coherently.

The finite-naming part of that obstruction has now been removed.
`stabilized-morita-branches-are-inner-but-incoherent` uses the explicit
two-by-two dilation

```text
[[s_i,A-s_it_i],[0,t_i]]
```

to realize each branch by inner conjugation in one fixed stabilization.
Thus finite algebraic naming of the branch maps is available.  What remains
is global coherence: local conjugate signs and pairwise contextual frame
transports must be aligned with one global prefix section.  The transition
elements fill an infinite frame stabilizer, so their centralizer fillings
are necessarily unbounded; property `(T)/(TT)` can replace that filling
only after an exact actor representation has been recovered.
