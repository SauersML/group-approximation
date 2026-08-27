# Nielsen--amalgam proof for the paired three-gate candidate

Write

```text
A=<h0,h2>=<a0,e0> = V4,
B=<k0,k1>=<a1,q1> = V4,
h=h1=q0 p1,
k=k2=p0 e1.
```

Here subscripts denote the two free factors `G0,G1` of `C=G0*G1`.
The paired relative relators are

```text
R0 = h0 z h z h2 z^(-1),
R1 = k0 z k1 z k z^(-1).                              (NA1)
```

The proof has two independent Nielsen normal-form steps.

## 1. The corner subgroup has no hidden long identities

Let

```text
Q = A * B * F(h,k).
```

Map `Q` to `C` by the displayed corner formulas.  A reduced `Q`-word is
expanded letter by letter in the free-product normal form of `G0*G1`:

```text
h     = q0 | p1,       h^(-1) = p1^(-1) | q0,
k     = p0 | e1,       k^(-1) = e1 | p0^(-1).          (NA2)
```

At a boundary with a nontrivial `A`-syllable, cancellation to the identity
would require `q in A` or `p in A`.  At a boundary with a nontrivial
`B`-syllable it would require `p in B` or `e in B`.  Inside a reduced word in
`F(h,k)`, the only same-copy products not belonging to an excluded inverse
pair are

```text
p e, e p^(-1) in G1,       q p, p^(-1) q in G0.        (NA3)
```

All are nonidentity.  Therefore no boundary merge deletes a whole syllable,
and after every allowed merge the adjacent factors again alternate.  The
expanded word is a nonempty `G0*G1` normal form.

The exclusions are literal matrix facts.  `A` consists of the four
`x_12`-matrices with parameters `0,s0,t1,s0+t1`.  The element
`q=x_34(s1)x_(11,12)(t0)` has different root support, and the 20-cycle `p`
is not unipotent.  Similarly `B={1,a,q,aq}` does not contain `p` or
`e=x_12(t1)`.  A permutation matrix cannot equal any of `q,e`; hence all
four products in `(NA3)` are nonidentity.  Thus

```text
Q -> C=G0*G1                                                   (NA4)
```

is injective.  In particular every actual identity in the six corner labels
is already a consequence of the two `V4` factors and free reduction.  The
``long coefficient identity'' residue is empty in every length, not merely
through eleven.

## 2. Tietze elimination gives a second Nielsen embedding

First impose `(NA1)` over the abstract coefficient group `Q`:

```text
P=<Q,z | R0,R1>.
```

Put `x=h0`, `y=h2`, `u=k0`, `v=k1`, and `s=z^(-1)`.  Each relator contains
one of the free generators `h,k` exactly once, so Tietze elimination gives

```text
h = z^(-1) x z y z^(-1) = s x s^(-1) y s,
k = z^(-1) v z^(-1) u z = s v s u s^(-1),             (NA5)
```

and

```text
P is isomorphic to L=A*B*<s>.
```

It remains to check that the induced map `Q -> L` is injective.  Expand the
four free letters as

```text
h      = s x s^(-1) y s,
h^(-1) = s^(-1) y s x s^(-1),
k      = s v s u s^(-1),
k^(-1) = s u s^(-1) v s^(-1).                         (NA6)
```

Every `A`- or `B`-syllable adjoining an `F(h,k)` block is separated from it
by a nonzero `s`-syllable.  Within a reduced `F(h,k)` word, equal signs of
successive terminal/initial `s`-powers combine to a nonzero power.  The only
opposite-sign joins either are the four excluded inverse pairs or expose one
of

```text
xv, xu, ux, vx, uv, vu.                                (NA7)
```

The first four are already reduced `A*B` words, while `uv=vu` is the third
nontrivial element of `B=V4`.  Hence an allowed join never vanishes and never
starts a cancellation cascade.  Every nontrivial reduced `Q`-word has a
nonempty `A*B*<s>` normal form.  Therefore

```text
Q -> P is injective.                                   (NA8)
```

## 3. Pushout and coefficient injectivity

The original paired quotient is the pushout

```text
Gamma = (C*<z>)/<<R0,R1>> = C *_Q P.                   (NA9)
```

Both edge maps are injective by `(NA4)` and `(NA8)`.  The normal-form theorem
for free products with amalgamation therefore injects `C=G0*G1` into
`Gamma`.  This is exactly the coefficient Freiheitssatz required for the
Kervaire--Laudenbach test.  The paired three-gate candidate is fenced.

## Corridor interpretation

Refine a coefficient region using the exact presentation
`Q=V4*V4*F2`.  The `h0/h2` and `k0/k1` gate squares form ordinary
one-dimensional corridors (commuting squares let the two gate colors cross
but do not branch).  A maximal internal endpoint would have to lie on a
coefficient face whose label is an actual identity outside `Q`.  Equation
`(NA4)` says no such face exists.  Thus gate corridors have no genuine long
Leavitt termination mechanism; after refinement they continue to the outer
boundary or close.  A closed configuration with a nontrivial outer label
would contradict the amalgam normal form `(NA9)`.

This explains why finite areas six, eight, and ten kept closing while the
weight test failed: the obstruction is Nielsen normal form, not curvature.
