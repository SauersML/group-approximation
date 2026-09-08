# Invariant random subgroups from the full Leavitt character simplex

2026-09-08. Written spectral, measure-theoretic, and group-theoretic
proof. No computation, build, or new Lean verification is asserted.

Let `R=L_(F_2)(1,2)` and `H=R^x`. The conclusion is

```text
IRS(H) = {(1-b) delta_({1}) + b delta_H : 0<=b<=1}.     (1)
```

Thus every probability-preserving action of `H` is essentially
free outside its global fixed set. This is a consequence of the
full character classification and simplicity, with an additional
return-probability argument recovering the actual subgroup law.
It is not a conclusion about matrix approximability.

## 1. The general statement and the missing measure-theoretic step

The proof works for any countably infinite group `G` satisfying

1. `G` has no proper subgroup of finite index;
2. every normalized positive-definite class function on `G` has
   the form `b*1+(1-b)*delta_1`, with `0<=b<=1`.

An invariant random subgroup, abbreviated IRS, is a
conjugation-invariant Borel probability measure on `Sub(G)`.
The subgroup space is viewed as a closed subset of `{0,1}^G`, so
membership events `{K:g in K}` are Borel. To an IRS `mu` associate

```text
phi_mu(g)=mu({K:g in K}).                              (2)
```

For every subgroup `K`, its membership function is the matrix
coefficient of the left quasi-regular representation on `l^2(G/K)`
at the unit vector `delta_K`:

```text
1_(g in K)=<lambda_K(g) delta_K,delta_K>.
```

Consequently (2) is normalized and positive definite. Conjugation
invariance of `mu` makes it a class function. The second hypothesis
therefore gives

```text
phi_mu=b*1+(1-b)*delta_1.                              (3)
```

Equation (3) alone is not being used as a general uniqueness theorem
for IRSs with specified characters. We will prove the extra identity

```text
b=mu({G}),                                            (4)
```

which is the decisive step for this particular character simplex.

## 2. A lazy return limit for every subgroup

Choose an enumeration `g_1,g_2,...` of `G`, and put

```text
lambda = sum_(j>=1) 2^(-j-1) (delta_(g_j)+delta_(g_j^(-1))),
nu = (delta_1+lambda)/2.
```

Both are probability measures. They are symmetric, and `lambda`
and `nu` have full support. This countable construction needs no
finite-generation hypothesis.

In any unitary representation `rho`, the norm-convergent sum

```text
A_rho=sum_(g in G) nu(g) rho(g)
```

is a positive self-adjoint contraction: it equals `(I+B)/2`,
where `B=sum_g lambda(g)rho(g)` is a self-adjoint contraction.
Its fixed vectors are exactly the `G`-fixed vectors. Indeed,

```text
2 <(I-A_rho)xi,xi>
  =sum_(g in G) nu(g) ||rho(g)xi-xi||^2,                (5)
```

and every weight is positive. Thus the left side is zero precisely
when every `rho(g)` fixes `xi`.

By spectral calculus on `[0,1]`, the powers `A_rho^n` converge
strongly to the orthogonal projection onto `ker(I-A_rho)`: the
scalar functions `t^n` converge to `1_({1})(t)` and are bounded
by one. Apply this to `rho=lambda_K`, and write `nu^{*n}` for
the `n`-fold convolution power. Then

```text
nu^{*n}(K)
 =sum_(g in K) nu^{*n}(g)
 =<A_(lambda_K)^n delta_K,delta_K>
 --> 1/[G:K].                                        (6)
```

Here `1/[G:K]` is defined to be zero when the index is infinite.
To verify the final value, the transitive action on `G/K` has
only constant invariant functions. If the index is `m<infinity`,
the projection of `delta_K` onto the normalized constant function
has squared norm `1/m`. If the index is infinite, there is no
nonzero square-summable constant function and the projection is
zero. In particular, infinitude of `G` gives

```text
nu^{*n}(1) --> 0.                                    (7)
```

No convergence rate, or uniformity in `K`, has been assumed.

## 3. Recovering the whole-group atom and the complete IRS law

For each `n`, Tonelli's theorem and (2) give

```text
integral_(Sub(G)) nu^{*n}(K) dmu(K)
 =sum_(g in G) nu^{*n}(g) phi_mu(g)
 =b+(1-b)nu^{*n}(1).                                 (8)
```

The functions `K -> nu^{*n}(K)` are Borel, being countable sums
of nonnegative multiples of membership indicators, and lie in
`[0,1]`. Dominated convergence in (6), together with (7)--(8),
therefore proves

```text
integral_(Sub(G)) 1/[G:K] dmu(K)=b.                   (9)
```

The first group hypothesis makes the integrand equal to
`1_({G})(K)`. This proves (4).

For every `g!=1`, subtracting the whole-group atom from its
membership event now gives

```text
mu({K:K!=G and g in K})=phi_mu(g)-mu({G})=0.          (10)
```

Every nontrivial proper subgroup contains some nonidentity
element. Because `G` is countable, the union of the events in
(10) still has measure zero. Thus `mu` is supported on `{1}`
and `G`, with masses `1-b` and `b`. Conversely, every such
mixture is invariant under conjugation. This proves the general
classification, including its endpoint cases `b=0,1`.

## 4. Verification of the hypotheses for the binary Leavitt group

The ring `R` is countable, since it is generated as an algebra
over the finite field `F_2` by four elements and every expression
is finite. Its unit group `H` is therefore countable. It is
infinite: its degree-zero matrix tower has finite subgroups of
unbounded order.

The established prefix identification and simplicity theorem give
`H=GL_4(R)=EL_4(R)` as an infinite simple group. Such a group has
no proper finite-index subgroup. Otherwise its action on the
finitely many cosets of such a subgroup would give a homomorphism
to a finite symmetric group. Simplicity makes the kernel either
trivial or all of `H`; injectivity into a finite group is impossible,
and a trivial coset action is transitive only on one coset.

Finally,
[the root fixed-projection theorem](../leavitt-root-fixed-projections-equal-the-global-fixed-projection.md)
includes the full character formula

```text
phi=phi(u)*1+(1-phi(u))*delta_1,
0<=phi(u)<=1.
```

Its proof is supplied independently in
[the elementary character artifact](leavitt-root-projections-and-elementary-character-proof-2026-09-08.md).
The group-theoretic input is
[the established simplicity theorem](../binary-leavitt-elementary-group-is-simple.md).
These verify both hypotheses of Section 1, proving (1) without
depending on a separate uncommitted character proof or a
finite-simple-group character estimate.

## 5. Probability-preserving actions

Let `H` act measurably and preserve the probability measure `m`
on a standard probability space `X`. The stabilizer map

```text
Stab:X -> Sub(H),       Stab(x)={g:gx=x}
```

is measurable because all its membership events are the measurable
fixed sets of individual group elements. It is equivariant:
`Stab(gx)=g Stab(x) g^(-1)`. Probability preservation therefore
makes its pushforward law an IRS.

Applying (1), almost every stabilizer is either `{1}` or `H`.
More explicitly, let

```text
X^H={x:gx=x for every g in H},
X_free={x:gx!=x for every g!=1}.
```

Both sets are measurable and invariant, since the group is
countable. They are disjoint, and their union is conull. Thus the
action on the complement of `X^H` is essentially free. Also, for
each `g!=1`, the set `Fix(g)\X^H` is null. Every ergodic action
is consequently either essentially free or fixes almost every
point. Equivalently, the only ergodic IRSs are the two point
masses in (1).

## 6. Scope for the approximation problem

This conclusion classifies exact subgroup-valued invariant laws and
the stabilizers of genuine probability-preserving actions. It does
not assert a quantitative version for approximate actions or a
finite list of relations detecting the classification.

The law `delta_({1})` has the regular character, while `delta_H`
has the trivial character. Thus the IRS classification constructs
no new nonembeddable character and leaves matrix approximability
of the regular character unresolved. No nonhyperlinearity
conclusion is drawn.
