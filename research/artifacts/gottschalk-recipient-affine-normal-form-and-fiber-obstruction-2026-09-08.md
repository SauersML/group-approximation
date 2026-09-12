# Recipient affinity does not supply a known bijective fiber

Date: 2026-09-08. Exact stable normal form and scoped obstruction.
No computation is used. Gottschalk's conjecture remains unresolved.

The purpose is to test a proposed extension of the homogeneous
[two-block elimination lemma](gottschalk-quadratic-block-elimination-2026-09-08.md)
against the universal
[three-factor reduction](gottschalk-stable-three-factor-reduction-2026-09-08.md).
The distinction between a bijective coordinate restriction and an
invariant coordinate fiber is essential.

## 1. Universal recipient-affine normal form

Let `R=Z/qZ`, `q>=2`, put `X=R^G`, and let `F:X -> X` be any cellular
automaton. The same construction works for a finite block of tracks
over any finite commutative ring. Define

```
H(x,u)=(x+u,F(x)-x-u).                              (1)
```

This is stably equivalent to `F` by reversible local changes. Indeed,

```
S(x,u)=(x,u+x),
T(y,v)=(v,y-v),
H=T o (F × id_X) o S.
```

The inverse of `S` subtracts `x` from the second track; the inverse of
`T` sends `(z,w)` to `(z+w,z)`. These are pointwise linear changes over
`R`, requiring no division.

For fixed `u`, the first output in (1) is a bijective affine function of
its entire recipient track `x`, with coefficient `id_X`. For fixed `x`,
the second output is a bijective affine function of its entire
recipient track `u`, with coefficient `-id_X`. These assertions concern
the full tracks, not merely one-site conditional permutations.

The construction preserves a bound of three unary lookup factors per
term, or a bound of three on ordinary polynomial degree over a finite
field, when `F` already has the corresponding form. For a finite block
of input tracks, every individual output coordinate likewise has a
constant invertible coefficient on its own recipient track; all
nonlinearity in that row is on the opposite block.

Consequently Gottschalk's assertion is equivalent to its restriction
to the family (1). Recipient affinity, constant invertible recipient
coefficients, and the three-factor bound can all be imposed at once
without removing the general problem.

## 2. Exact images, collisions, and genuine certificate fibers

The full fiber structure is explicit:

```
H(x,u)=(z,w)  iff  F(x)=z+w and u=z-x.
```

Thus `H^-1(z,w)` is in canonical bijection with `F^-1(z+w)`, and

```
im H = {(z,w): z+w∈im F}.
```

In particular `H` is injective exactly when `F` is injective, and
surjective exactly when `F` is surjective. Equivalently,

```
H(x,u)=H(x',u')
  iff F(x)=F(x') and x+u=x'+u'.
```

The restriction of the second output to `x=0` is the bijection
`u -> F(0)-u`. However,

```
H(0,u)=(u,F(0)-u),
```

so the zero-`x` axis is not invariant. Calling the second-coordinate
restriction a bijective invariant fiber would be false.

The pointwise linear input change `(z,x) -> (x,z-x)` does isolate an
actual preserved certificate. It turns (1) into

```
K(z,x)=(z,F(x)-z).                                  (2)
```

For every certificate configuration `z`, its fiber map is a translate
of `F`. Any one such fiber is bijective if and only if `F` is bijective;
when one is bijective, all are. No particular certificate provides an
independently known bijection. In addition, (2) is affine in the second
recipient block if and only if `F` itself is affine. This canonical
certificate isolation therefore does not retain recipient affinity
for a non-affine `F`.

These are equivalences for the displayed changes. They do not assert
that every possible sequence of nonlinear reversible shears has the
same limitation.

## 3. The correct graph replacing the zero axis in an affine lemma

For comparison, consider a CA on two full-shift blocks of the form

```
P(x,u)=(L_u x+b(u), V(x,u)),
```

and assume each `L_u` is bijective and linear in `x`. The coefficient
map `E(x,u)=(L_u x+b(u),u)` is then a bijective CA: each fiber is
bijective, and its local inverse follows from compactness and
equivariance. Its inverse is

```
E^-1(z,u)=(L_u^-1(z-b(u)),u).
```

The transformed map `P E^-1` preserves `z`. Its zero-certificate fiber
is therefore

```
u -> V(-L_u^-1 b(u),u),                             (3)
```

which lies over a generally moving graph in the old coordinates.
It is not `u -> V(0,u)`. If `P` is injective and (3) is known bijective,
then `P` is surjective. To check this directly, write `D=P E^-1`.
For a finitely supported certificate `z`, its fiber map differs from
the bijective zero-certificate fiber in only finitely many output
coordinates, by locality. An injective finite-output perturbation of
a bijection is bijective: compose with the old inverse, fix the
unchanged exterior output, and count the finite interior possibilities.
Thus all these certificate fibers are onto. They form a dense subset
of the full output space, and compactness makes the image of `D`
closed. Hence `D`, and then `P`, is surjective. In (1),
`L_u=id`, `b(u)=u`, and (3) is `u -> F(-u)`. The missing hypothesis is
therefore precisely the original unknown bijectivity.

## 4. A stronger obstruction for constant linear two-track changes

There is a rigorous limitation beyond the particular isolation (2).
Let `k` be a finite field and let `F:k^G -> k^G` be non-affine over `k`.
Take arbitrary constant invertible matrices

```
U=[[a,b],[c,d]],       V=[[p,q],[r,s]] ∈ GL_2(k),
```

acting pointwise on two tracks, and set `J=V(F × id)U`. Its components
are

```
J_1(x,u)=p F(ax+bu)+q(cx+du),
J_2(x,u)=r F(ax+bu)+s(cx+du).
```

If `J_1` is affine in its own track `x` for every fixed `u`, then
`pa=0`: otherwise setting `u=0` leaves an invertible scalar change of
the non-affine `F`, plus a linear map. Similarly recipient affinity of
`J_2` forces `rb=0`.

Invertibility of `U,V` consequently leaves exactly two cases. If
`a!=0`, then `b=p=0` and `d,q,r!=0`. Hence

```
J_1(x,u)=qc x+qd u,
J_2(x,u)=r F(ax)+sc x+sd u.
```

For a fixed `x`, the first expression varies nontrivially with `u`.
For a fixed `u`, the second expression is non-affine, and in particular
nonconstant, in `x`. Neither coordinate fiber can be sent into a fixed
fiber of that same coordinate. In the other case `b!=0`, interchange
the two roles: `a=r=0`, `c,p,s!=0`, and the same conclusion follows.

Thus no constant linear two-track reparametrization of `F × id` can
simultaneously be affine in each own recipient track and preserve a
coordinate axis, or even send a fixed coordinate fiber into another
fixed fiber of that coordinate. The theorem does not cover arbitrary
nonlinear shears, additional tracks, or spatially varying linear
operators.

## 5. Reversible control and the remaining unknown

This obstruction is compatible with reversibility. Over `F_2`, let
`t∈G` have order three and take the previously verified scalar CA

```
F(x)(g)=x(g)+x(g)x(gt)+x(gt)x(gt^2).
```

It fixes the zero, one, and weight-one patterns on each three-site
coset, and cycles the three weight-two patterns; hence `F^3=id`.
It is non-affine. Its stabilization (1) is reversible and affine in
both own recipient tracks, yet Section 4 prevents the specified
constant linear normalization from producing an invariant coordinate
fiber while retaining that affinity.

The established positive elimination theorem requires a genuine
homogeneous block and a proved bijection on the appropriate
fiber. Replacing these with recipient affinity and a bijective
coordinate restriction already includes every original CA through
(1). Whether every injective member of that universal family is
surjective is exactly the unresolved headline assertion.
