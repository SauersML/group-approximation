# Equivariant fiber functors reduce exactly to stabilizer intertwiners

Date: 2026-08-11

## 1. Outcome

The remaining simultaneous-coherence equation from
`FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md` is

`Pi_(i,kx)(alpha_k g)=Ad(zeta_i(k,x)) Pi_(i,x)(g).`       `(EFR1)`

On a transitive finite base orbit, there is no need to solve for an
independent representation `Pi_(i,x)` at every point.  The entire family is
determined by one representation at one basepoint.  The only existence
condition is covariance under the basepoint stabilizer.

For two sectors, agreement on the positive window reduces to an explicit
finite list of conjugacy equations involving the **relative holonomy**

`t(k)=zeta_1(k,x_0)^* zeta_0(k,x_0).`                    `(EFR2)`

This is the minimum-variable form of the remaining finite
Fourier/Frobenius problem.  It also gives a sharp same-bundle obstruction:
if the two external cocycles coincide, agreement on a window over every
base point forces agreement on its full external-group saturation.  Thus a
marked Laurent label lying in that saturation cannot retain a fold.

The theorem is exact and does not invoke numerical matrix search.

## 2. One equivariant family

Let a finite group `K` act transitively on a finite set `X`.  Let `G` be a
group and let

`alpha:K -> Aut(G)`                                         `(EFR3)`

be an action.  Fix a finite-dimensional Hilbert space `V` and a unitary
cocycle

`zeta:K times X -> U(V)`                                    `(EFR4)`

with convention

`zeta(kl,x)=zeta(k,lx) zeta(l,x).`                          `(EFR5)`

An equivariant fiber functor is a family of representations

`Pi_x:G -> U(V)`                                            `(EFR6)`

satisfying `(EFR1)` without the sector index.

Choose `x_0 in X` and put

`H=Stab_K(x_0).`                                            `(EFR7)`

**Theorem 1 (stabilizer reduction).**  Restriction to `x_0` is a bijection
between equivariant families `(EFR6)` and representations

`pi:G -> U(V)`                                              `(EFR8)`

satisfying

`pi(alpha_h g)=Ad(zeta(h,x_0)) pi(g)`                       `(EFR9)`

for every `h in H` and `g in G`.

Given `pi`, the corresponding family is

`Pi_(k x_0)(g)`
` =Ad(zeta(k,x_0)) pi(alpha_(k^(-1)) g).`                   `(EFR10)`

### Proof

Necessity of `(EFR9)` follows from `(EFR1)` with `x=x_0` and `h in H`.

Conversely, define `(EFR10)`.  It is independent of the representative of
the coset `kH`.  Indeed, if `k'=kh` with `h in H`, then `(EFR5)` gives

`zeta(kh,x_0)=zeta(k,x_0)zeta(h,x_0)`,                     `(EFR11)`

while `(EFR9)`, applied with `alpha_(h^(-1)k^(-1))g`, gives

`Ad(zeta(h,x_0))`
` pi(alpha_(h^(-1)k^(-1))g)`
` =pi(alpha_(k^(-1))g).`                                   `(EFR12)`

Equations `(EFR11)--(EFR12)` prove well-definedness.

For `l,k in K`, formula `(EFR10)` and the cocycle identity give

`Pi_(lkx_0)(alpha_l g)`
` =Ad(zeta(l,kx_0)zeta(k,x_0))`
`   pi(alpha_(k^(-1))g)`
` =Ad(zeta(l,kx_0)) Pi_(kx_0)(g).`                         `(EFR13)`

Thus `(EFR1)` holds.  Formula `(EFR10)` also proves uniqueness.  End proof.

For a nontransitive finite base, apply Theorem 1 independently to one
basepoint in each orbit.

## 3. Two sectors and relative holonomy

Let `zeta_0,zeta_1` be two cocycles on the same transitive base and let
`pi_0,pi_1` satisfy their respective stabilizer equations `(EFR9)`.  Denote
the induced families by `Pi_(0,x),Pi_(1,x)`.

For `k in K`, define `t(k)` by `(EFR2)`.  Let `P subset G` be the tested
positive window.

**Theorem 2 (basepoint agreement criterion).**  The two families agree on
`P` at every base point,

`Pi_(0,x)(g)=Pi_(1,x)(g)` for all `x in X`, `g in P`,      `(EFR14)`

if and only if

`pi_1(alpha_(k^(-1))g)`
` =Ad(t(k)) pi_0(alpha_(k^(-1))g)`                         `(EFR15)`

for every `k in K` and `g in P`.

### Proof

Substitute `(EFR10)` for the two sectors at `x=kx_0`.  Equality becomes

`Ad(zeta_0(k,x_0)) pi_0(alpha_(k^(-1))g)`
` =Ad(zeta_1(k,x_0)) pi_1(alpha_(k^(-1))g).`               `(EFR16)`

Conjugating `(EFR16)` by `zeta_1(k,x_0)^*` gives exactly
`(EFR15)`.  End proof.

Thus all apparent fiber variables disappear.  The data to solve for on one
orbit are only

1. two basepoint representations `pi_0,pi_1`;
2. their two stabilizer covariance laws; and
3. the finite relative-holonomy table `t(k)` acting on the external
   saturation of `P`.

The table `t(k)` is not arbitrary: it is determined by the two exact
principal-bundle cocycles.  Its consistency under changing `k` by an element
of `H` is automatic from `(EFR5)` and the two stabilizer equations.

## 4. The averaged marked energy is also a basepoint statistic

For any marked `m in G`, the squared normalized-Hilbert--Schmidt distance
between the two global block-diagonal fiber operators is

`D_X(m)^2=(1/|X|) sum_(kH in K/H)`
` ||Ad(zeta_0(k,x_0)) pi_0(alpha_(k^(-1))m)`
`   -Ad(zeta_1(k,x_0)) pi_1(alpha_(k^(-1))m)||_2^2.`        `(EFR17)`

Equivalently, by unitary invariance,

`D_X(m)^2=(1/|X|) sum_(kH in K/H)`
` ||Ad(t(k)) pi_0(alpha_(k^(-1))m)`
`   -pi_1(alpha_(k^(-1))m)||_2^2.`                         `(EFR18)`

Therefore the required positive-window/fold separation is precisely:

* `(EFR15)` holds, exactly or outside a vanishing-rank part, on the tested
  positive labels; while
* `(EFR18)` stays bounded away from zero on the marked Laurent label.

This is a finite representation-theoretic incidence problem.  It is not a
dense optimization over one unrelated unitary family per base point.

## 5. Same external cocycle no-go

Suppose

`zeta_0=zeta_1`.                                           `(EFR19)`

Then `t(k)=1` for every `k`, and `(EFR15)` says

`pi_0(a)=pi_1(a)`                                         `(EFR20)`

for every

`a in K^(-1)P={alpha_(k^(-1))g:k in K,g in P}.`           `(EFR21)`

**Corollary 3 (saturation obstruction).**  Under `(EFR19)`, if the marked
label `m` belongs to the external saturation `(EFR21)`, common-positive
agreement on every base point forces `D_X(m)=0`.

This shows that merely allowing the tangent embedding to depend on the base
does not help when both sectors use the same external principal bundle.  A
live construction must use nontrivial relative holonomy `t(k)` and arrange
that it is invisible on the positive saturation while remaining visible in
the average `(EFR18)`.

For Laurent monomial actions this obstruction is substantial: external
special-linear substitutions can send a positive coordinate direction to
its negative using a determinant-one sign change in two coordinates.  Thus
the external saturation of even a very small positive monomial window can
already contain inverse monomials.  The difference between the two
principal-bundle cocycles is load bearing, not optional.

## 6. Exact remaining theorem

In the paired Fourier/Frobenius construction, `G` is the finite square-zero
base/tangent group, `K` is the selected finite external congruence image,
and `P` is the finite positive coefficient window.  The local compressor
construction already supplies the required pair along the selected cyclic
subgroup.  The unresolved globalization can now be stated without any
fiberwise redundancy:

> Construct finite Frobenius modules and basepoint representations
> `pi_(0,n),pi_(1,n)` satisfying the two stabilizer covariance equations and
> `(EFR15)` on the growing positive window, possibly after deleting a
> vanishing-rank part, while the marked average `(EFR18)` has a fixed positive
> lower bound.

The cyclic monodromy theorem in
`FALSE_LONG_CHAIN_BUNDLE_MONODROMY_NO_GO.md` proves that the naive long-chain
basepoint pair fails this criterion.  The present reduction identifies the
minimal replacement: a pair of stabilizer-intertwining Frobenius
representations with nontrivial relative holonomy.
