# TRUE: projective towers reduce to an integral saturation quotient

Date: 2026-08-11

## Outcome

The maps

```text
P^2(Z/p^(k+1)Z) -> P^2(Z/p^k Z)                    (PTS1)
```

have constant fibre size `p^2`.  Pullback along (PTS1) is an isometry for
normalized Euclidean norms, commutes with every fixed group-ring cellular
boundary, and preserves integral coordinates.  Consequently, an integral
circle decoder at level `p^k` pulls back to the literal oldclass image at
level `p^(k+1)` with **no increase in its normalized operator norm**.

This isolates the only possible new tower obstruction.  Inside the old real
harmonic subspace, the upper-level integral harmonic lattice can be larger
than the pulled-back lower-level lattice.  The finite quotient between them
is an integral saturation quotient.  Ordinary pullbacks are harmless; only
the new fractional cosets in this quotient need a new paired-discriminant
estimate.

## 1. Constant-fibre pullback

Let `Gamma` act on finite sets `X` and `Y`, and suppose

```text
pi:Y->X                                                    (PTS2)
```

is a `Gamma`-equivariant surjection with every fibre of cardinality `d`.
Give real-valued functions the normalized norms

```text
||f||_X^2=(1/|X|) sum_(x in X)|f(x)|^2,
||h||_Y^2=(1/|Y|) sum_(y in Y)|h(y)|^2.                   (PTS3)
```

Define `Jf=f compose pi`.

**Lemma 1 (isometric integral pullback).**

```text
||Jf||_Y=||f||_X,                                         (PTS4)
J(Z^X) subset Z^Y.                                        (PTS5)
```

The same identities hold for any fixed finite direct sum of copies of the
function spaces.

**Proof.**  Since `|Y|=d|X|`,

```text
||Jf||_Y^2
 =1/(d|X|) sum_(x in X) sum_(y in pi^(-1)(x)) |f(x)|^2
 =||f||_X^2.
```

Integer-valued functions plainly pull back to integer-valued functions.
End proof.

Let `g in Gamma` act by `(g f)(x)=f(g^(-1)x)`.  Equivariance of `pi` gives

```text
J(gf)=g(Jf).                                               (PTS6)
```

It follows entrywise that `J` commutes with every matrix over `Z Gamma`.

## 2. No norm growth for literal oldclass repair

Let

```text
A in M_(r by s)(Z Gamma)                                  (PTS7)
```

be any fixed relation or cellular matrix.  Write `A_X,A_Y` for its actions
on the two finite coefficient sets and `J_r,J_s` for componentwise pullback.
Equation (PTS6) gives the exact commutative square

```text
A_Y J_s = J_r A_X.                                        (PTS8)
```

This applies equally to real vectors, integer carries, and circle-valued
vectors because all operations are coordinatewise and integral.

**Theorem 2 (oldclass decoder transfer).**  Suppose a collection of
circle-valued inputs at `X` admits integral repairs with constant `C`: for
each input `a`, there is an integral correction `z_a` satisfying the exact
target equations and

```text
||z_a||_X <= C defect_X(a).                               (PTS9)
```

Then every pulled-back input `J a` at `Y` has the pulled-back integral repair
`J z_a`, and

```text
||J z_a||_Y <= C defect_Y(Ja) = C defect_X(a).            (PTS10)
```

**Proof.**  Exactness follows from (PTS8), integrality from (PTS5), and the
two norm equalities from (PTS4), applied to the correction and to every
fixed relation coordinate in the defect.  End proof.

The theorem is one-sided.  Averaging an arbitrary upper-level integral
repair down a fibre generally introduces denominators, so it does not imply
equality of the unrestricted repair constants.

## 3. The saturation quotient

Use the harmonic lift sequence of
`TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md` at the two levels:

```text
0 -> L_X -> M_X -> Q_X^# -> 0,
0 -> L_Y -> M_Y -> Q_Y^# -> 0.                            (PTS11)
```

Use the same fixed group-ring boundary matrices and compatible pulled-back
spherical templates at both levels.  The image of `J` is a reducing subspace
for every group element and hence for every boundary and its adjoint.
Therefore harmonic vectors pull back to harmonic vectors.  The cellular
pullbacks induce a commuting morphism from the first row of (PTS11) to the
second.  In particular, if `s_X:Q_X^#->M_X` is an integral section, then

```text
J_M s_X:Q_X^# -> M_Y                                     (PTS12)
```

is an integral lift of the pulled-back lattice `J_Q(Q_X^#)`.  The inclusion
`J_Q(Q_X^#) subset Q_Y^#` uses the unnormalized integral lattice pairing:
for an upper integral cycle `c`,

```text
<J_Q u,c>_Y=<u,pi_* c>_X in Z.                           (PTS12a)
```

Here `pi_*` sums coordinates in each fibre and is an integral chain map.
Unnormalized norms on both the harmonic vector and its lift are multiplied
by `sqrt(d)`; equivalently, normalized norms are unchanged.  In either
convention the section ratio, hence the operator norm relevant to repair, is
exactly the norm of `s_X`.

Let `H_old=span_R J_Q(Q_X^#)` inside the upper harmonic space and define

```text
Q_(Y,old)^# = Q_Y^# intersect H_old,
Sat(Y/X) = Q_(Y,old)^# / J_Q(Q_X^#).                      (PTS13)
```

The denominator in (PTS13) has full rank in `H_old`, so `Sat(Y/X)` is finite.
It measures precisely the failure of the pulled-back integral dual lattice
to be primitive in the upper-level lattice.

**Theorem 3 (tower saturation reduction).**

1. Every class in `J_Q(Q_X^#)` has a decoder with the lower-level section
   constant.
2. If `Sat(Y/X)=0`, the entire upper-level integral lattice in the old real
   harmonic subspace has the same bound.
3. In general it is enough to choose one shortest representative of every
   nonzero class of `Sat(Y/X)` and bound its paired integral lift.  If the
   lower section constant is `C` and those representatives have lift ratios
   at most `K`, then `2C+K` is a valid bound on all of `Q_(Y,old)^#`.

**Proof.**  Part 1 is (PTS12).  Part 2 is the equality of the two lattices in
(PTS13).  For part 3, choose in each coset a shortest representative `u_c`
and an integral lift `z_c` with `||z_c||<=K||u_c||`.  Write

```text
u=J_Q(v)+u_c.
```

Because `u_c` is shortest in its coset, `||u_c||<=||u||`, and hence

```text
||J_Q(v)||<=||u||+||u_c||<=2||u||.                      (PTS13a)
```

The vector `J_M s_X(v)+z_c` is an integral lift of `u`, of norm at most
`(2C+K)||u||`.  The zero coset uses the lower section directly.  End proof.

The quantitative bound from arbitrary representatives need not be optimal,
but the exact paired-discriminant formula can optimize each finite coset.

There is also a uniform algebraic restriction on this finite quotient.

**Theorem 4 (degree kills the saturation quotient).**  In the setup above,

```text
d Sat(Y/X)=0.                                             (PTS13b)
```

If the old harmonic rank is `r`, then

```text
|Sat(Y/X)|<=d^r.                                          (PTS13c)
```

**Proof.**  Write `u=J_Q(v)` in the old real harmonic subspace and suppose
`u in Q_Y^#`.  For every element `q` of the lower primal harmonic lattice,
its integral pullback `Jq` is an upper primal harmonic element.  Using the
unnormalized pairing and `J^*J=dI`,

```text
<d v,q>_X=<Jv,Jq>_Y=<u,Jq>_Y in Z.
```

Thus `dv in Q_X^#`, so `du=J_Q(dv)` lies in the denominator of (PTS13).
This proves (PTS13b).  A finite quotient of two rank-`r` lattices killed by
`d` is generated by at most `r` elements of orders dividing `d`, which gives
(PTS13c).  End proof.

## 4. Application to projective prime-power towers

Reduction modulo `p^k` gives the equivariant map (PTS1).  Formula

```text
|P^2(Z/p^k Z)|=p^(2(k-1))(p^2+p+1)                       (PTS14)
```

shows that every fibre has size `p^2`: equivariance makes all fibres have the
same size, and the ratio in (PTS14) is `p^2`.  Therefore Lemma 1 and Theorems
2--3 apply at every step of a fixed `p`-power tower.

Theorem 4 gives the sharper stepwise restriction

```text
p^2 Sat(p^(k+1)/p^k)=0,
|Sat(p^(k+1)/p^k)|<=p^(2r).                              (PTS14a)
```

Thus a prime-power tower cannot create arbitrary new denominators in one
step.  It creates at most two new `p`-primary layers in each old harmonic
direction.  Across many steps these layers may accumulate, so (PTS14a) is
not by itself a uniform decoder; it identifies the exact primary filtration
that must be split with controlled norm.

This changes the correct computational target.  One should not repeatedly
recompute a decoder on the entire upper harmonic plane.  Instead compute

```text
Sat(p^(k+1)/p^k)                                         (PTS15)
```

and the paired lift distortion of its new cosets.  There are three possible
outcomes:

* the saturation quotients vanish, so old real directions are uniformly
  controlled for free;
* their exponents grow but every new coset has a uniformly comparable
  integral lift, still supporting TRUE;
* a sequence of new fractional cosets has harmonic norm tending to zero
  while its minimum integral lift stays macroscopic, producing the exact
  denominator/numerator collapse isolated by `(HIL22)`.

The last two cases concern integral refinements, not ordinary pullback of
cuspidal classes.

## 5. Scope and next exact test

This theorem does not control genuinely new real harmonic packets at higher
level, and it does not prove a bound for the saturation cosets.  It does
remove a misleading source of apparent growth: duplicating a lower-level
repair across a constant-fibre cover never worsens its normalized cost.

For the level-`121` calculation, exact rational ranks at level `11` give
`H_2=0`, while the independent modular/literature certificate at level
`121` gives harmonic rank seven.  Thus all seven upper-level directions are
genuinely new packets rather than oldclass saturation.
For towers above a level already carrying cuspidal homology, the additional
certificate should export both the new-real quotient and the integral
saturation group (PTS15).  That is the finite arithmetic object on which a
uniform tower proof must act.
