# STW LXXXVII: uniform Roe nuclear dimension audit (2026-08-30)

## Primary-source status

For a countable discrete bounded-geometry metric space `X`, Winter--Zacharias,
[Theorem 8.5](https://arxiv.org/abs/0903.4914), prove

```text
dim_nuc(C*_u(X)) ≤ asdim(X).
```

Li--Willett, [Theorem 2.2 and Remark
2.6](https://arxiv.org/abs/1705.01290), prove equality at asymptotic dimension
zero and observe that the upper bound then gives equality at value one.
Li--Liao--Winter, [Theorem 7.7](https://arxiv.org/abs/2303.16762), prove the
different statement

```text
dim_diag(ℓ^∞(X) ⊆ C*_u(X)) = asdim(X).
```

Their Remark 2.2(i) gives only `dim_nuc ≤ dim_diag`.  An arXiv title/abstract
search through 2026-08-30 found no subsequent primary source proving the
ordinary nuclear-dimension equality; in particular the finite case `X = ℤ²`
remains outside the located results.  Zhu--Zhang's transfinite nuclear dimension
is a one-sided transfinite upper bound, not the missing ordinary lower bound.

## Equality at infinity without property A

Sako, [Theorem 1.1](https://arxiv.org/abs/1212.5900), proves that property A is
equivalent to nuclearity of the uniform Roe algebra.  If `X` lacks property A,
then `C*_u(X)` is not nuclear, so its nuclear dimension is infinite because
finite nuclear dimension implies nuclearity.  Moreover `asdim(X)` cannot be
finite: Winter--Zacharias would then give finite nuclear dimension.  Hence

```text
X lacks property A  ⇒  dim_nuc(C*_u(X)) = asdim(X) = ∞.
```

This is an unconditional extension of the equality class in the extended
natural numbers, obtained by combining existing theorems; it is not asserted
to be a new literature theorem.

## Subspace-corner reduction

For `Y ⊆ X`, let `p_Y = χ_Y`.  Compression of a finite-propagation operator
on `ℓ²(X)` has the same propagation bound on `ℓ²(Y)`.  Conversely, zero
extension of a finite-propagation operator on `ℓ²(Y)` has the same bound on
`ℓ²(X)`.  Taking norm closures gives

```text
p_Y C*_u(X) p_Y = C*_u(Y).
```

Winter--Zacharias Proposition 2.5 says nuclear dimension does not increase on
hereditary subalgebras, so

```text
dim_nuc(C*_u(Y)) ≤ dim_nuc(C*_u(X)).
```

Consequently, if `asdim(X)=n` and `X` contains a subspace `Y` whose uniform Roe
algebra already has nuclear dimension `n`, then equality holds for `X`.  This
is a rigorous propagation theorem, not a solution: no finite seed `n≥2` is
produced here.

## Coarse-embedding corner reduction

The literal-subspace hypothesis can be removed.  Let `f:Y→X` be a coarse
embedding.  Effective properness makes all fibres of `f` uniformly bounded
in `Y`; bounded geometry then bounds their cardinalities by one finite `N`.
Label each fibre injectively by `{1,...,N}` and send

```text
δ_y ↦ δ_f(y) ⊗ e_c(y).
```

This isometry identifies `C*_u(Y)` with a diagonal corner

```text
p M_N(C*_u(X)) p,
p ∈ M_N(ℓ∞(X)).
```

Bornology of `f` sends finite propagation forward, while effective
properness sends finite propagation in the compressed corner back to finite
propagation on `Y`; hence the identification is onto the entire corner, not
merely an embedding.  Matrix invariance and hereditary monotonicity of
nuclear dimension give

```text
Y coarsely embeds in X
  ⇒ dim_nuc(C*_u(Y)) ≤ dim_nuc(C*_u(X)).
```

This functorial corner construction is consistent with the standard uniform
Roe functoriality recorded by Braga--Farah--Vignati, [*General uniform Roe
algebra rigidity*](https://doi.org/10.5802/aif.3461): injective coarse
embeddings give hereditary embeddings, while general coarse embeddings give
hereditary embeddings after stabilization.  The finite-fibre argument above
sharpens the stabilization to one finite matrix amplification in the present
bounded-geometry metric setting.

There are two exact consequences for the remaining LXXXVII regimes.

1. In finite asymptotic dimension `n≥2`, equality for one space `Y` propagates
   to every `X` of asymptotic dimension `n` into which `Y` coarsely embeds.
2. For a property-A space of infinite asymptotic dimension, coarse embeddings
   of spaces whose uniform Roe nuclear dimensions are unbounded force the
   target nuclear dimension to be infinite.

This is a strictly wider lower-bound mechanism than literal subspace
compression, but it does not manufacture the missing seeds: even the value
for `C*_u(ℤ²)` remains open here.  Coarse equivalences give embeddings in
both directions, so uniform Roe nuclear dimension, and therefore the truth of
the LXXXVII equality, is invariant under coarse equivalence.

## Why diagonal averaging does not give the reverse inequality

Assume `x≠y` in `X`.  In their two-point matrix corner set

```text
p = (e_xx + e_xy + e_yx + e_yy)/2,
q = (e_xx - e_xy - e_yx + e_yy)/2.
```

These are orthogonal rank-one projections, so the map from `ℂ²` sending its
minimal projections to `p,q` is a *-homomorphism and hence order zero.  For the
canonical diagonal expectation `E_X`, however,

```text
E_X(p) = E_X(q) = (e_xx+e_yy)/2,
E_X(p)E_X(q) = (e_xx+e_yy)/4 ≠ 0.
```

Thus postcomposition with `E_X` destroys order zero.  The obstruction is
quantitatively rigid.  If `theta:C^2->ell^infinity(X)` is c.p.c. order zero,
write `a=theta(e_1)` and `b=theta(e_2)`.  Coordinatewise positivity and
`ab=0` force at least one of `a(x),b(x)` to vanish, while both averaged
images take value `1/2` at `x`.  Therefore

```text
max_i norm(theta(e_i)-(E_X phi)(e_i)) >= 1/2.
```

The zero map attains equality, so the distance is exactly `1/2`.  This rules
out not only raw averaging of the return maps in a nuclear-dimension
approximation, but also any uniformly small perturbation of that averaged
two-point packet to a diagonal order-zero map.  It does not rule out a
subtler diagonal-recovery theorem which changes the approximation before
averaging.

There is a second, complementary obstruction for noncommutative colours.
Every order-zero positive functional on `M_n`, `n>=2`, is zero: diagonalize
the density matrix of a hypothetical nonzero functional, take a positive
eigenvector and an orthogonal vector, and rotate them to two orthogonal unit
vectors on whose rank-one projections the functional is strictly positive.
This contradicts preservation of orthogonality.  Composing an order-zero map

```text
theta:M_n->ell^infinity(X)
```

with every point evaluation therefore shows that `theta=0`.  More generally,
an order-zero map from a finite-dimensional algebra into the diagonal
vanishes on every noncommutative matrix summand.

If `M_n` is the matrix corner supported on `n` distinct points of `X`, the
diagonal expectation restricted to that corner has norm one.  Since zero is
the only diagonal c.p.c. order-zero competitor, its distance from every such
competitor is exactly one.  The earlier `C^2` calculation remains necessary
and nonredundant because scalar summands can survive in a commutative target;
it shows that even those colours can acquire a rigid one-half orthogonality
defect.  Together, the two calculations show that raw diagonal averaging
both destroys some commutative packets and discards every noncommutative
packet.  Neither calculation excludes a recovery argument that reorganizes
the approximation before applying the expectation.

## Z2 boundary and limit-operator firewall

The natural periodic-quotient route is unavailable even for `Z^2`.
Translation by a nonzero `h in Z^2` acts freely on `beta Z^2`: choose an
integer coordinate nonzero on `h` and partition its values modulo a prime
not dividing that coordinate.  Translation by `h` permutes the clopen cells
without a fixed cell, whereas an ultrafilter selects exactly one cell.  Thus
there are no finite orbits and no equivariant coefficient quotient

```text
ell^infinity(Z^2) -> C(F)
```

for a nonempty finite `Z^2`-set `F`.  The same argument excludes a
star-homomorphic retraction from `C*_u(Z^2)` to the canonical `C(T^2)` that
fixes the group unitaries: composing its diagonal restriction with a torus
character would give a translation-invariant character of
`ell^infinity(Z^2)`.

Limit operators have the complementary behavior.  The orbit-evaluation map
at every ultrafilter permutes each finite-index coset partition and fixes the
group unitaries.  Its crossed-product image therefore contains

```text
C(Z^2/H) crossed_product Z^2
 ~= M_[Z^2:H](C(T^2))
```

for every finite-index subgroup `H`.  For a boundary ultrafilter this image
is a quotient of the uniform Roe corona.  The two-dimensional periodic
blocks, including their Bott classes, survive only as subalgebras of that
quotient.  Since nuclear dimension is not monotone under arbitrary
subalgebras, this gives no lower bound.  Freeness simultaneously prevents
promoting the blocks through the canonical finite-orbit coefficient
quotient.  Hence crossed-product quotients, limit operators, K-theory, and
dynamic-asymptotic-dimension restrictions all stop at the same variance
barrier; none supplies `dim_nuc(C*_u(Z^2))>=2`.

## Exact remaining frontier

The cases not covered by the preceding established results are:

1. `2 ≤ asdim(X) < ∞`, where the missing statement is
   `dim_nuc(C*_u(X)) ≥ asdim(X)`;
2. `asdim(X)=∞` with property A, where `C*_u(X)` is nuclear but it is unknown
   here whether its nuclear dimension must be infinite.

No claim in this audit settles either frontier.
