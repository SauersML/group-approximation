# Compact actions cannot move the compressor anchor

Date: 2026-08-12

## 1. Outcome

Let `Gamma<G` be arbitrary, and suppose

```text
t Gamma t^(-1)<=Gamma.                                (CAN1)
```

For `gamma in Gamma`, put

```text
h=t^(-1) gamma t.                                     (CAN2)
```

Then every almost-periodic unitary representation `pi` of `G` satisfies

```text
pi(Gamma)' subset pi(h)'.                              (CAN2a)
```

Equivalently, `pi(h)` belongs to the bicommutant of `pi(Gamma)`.  In
particular, every compact probability-measure-preserving action of `G` has
the following rigidity:

```text
L^2(X)^Gamma subset L^2(X)^h.                         (CAN3)
```

In words, every `Gamma`-invariant measurable function is fixed by the
inverse predecessor `h`.  Consequently no compact action can furnish the
relative-commutant escape in
`FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`.

If `G` itself has property `(T)`, the same exclusion holds for every
ergodic weakly compact action.  Indeed property `(T)` upgrades weak
compactness to compactness by the invariant-vector argument in Ioana's
Section 6.

Thus a classical action capable of proving FALSE through the fixed
Kun--Thom double must be genuinely non-weakly-compact.  Profinite actions,
compact homogeneous actions, and actions orbit equivalent to a compact
action are all excluded at once.

## 2. Finite-dimensional intertwiner equality

The key point uses only finite dimensionality; property `(T)` is not needed
until the later passage from weakly compact to compact actions.

**Lemma 1 (every finite intertwiner propagates).**  Let

```text
rho_i:G->U(V_i),       i=0,1,
```

be finite-dimensional unitary representations.  If an operator

```text
T:V_1->V_0
```

intertwines their restrictions to `Gamma`, then it also intertwines `h`:

```text
rho_0(delta)T=T rho_1(delta)       (delta in Gamma)
  implies rho_0(h)T=T rho_1(h).                         (CAN4)
```

### Proof

On `Hom(V_1,V_0)` consider the finite-dimensional unitary representation

```text
beta(g)X=rho_0(g)X rho_1(g)^*.                         (CAN5)
```

The intertwiner space is `Fix_Gamma(beta)`.  Conjugating the fixed-space
equations gives

```text
beta(t)Fix_Gamma(beta)=Fix_(t Gamma t^(-1))(beta).      (CAN6)
```

The right-hand side contains `Fix_Gamma(beta)` by `(CAN1)`.  It has the
same finite dimension by `(CAN6)`, so equality holds.  Thus `beta(t)T` is
again `Gamma`-fixed, and

```text
beta(h)T
 =beta(t)^* beta(gamma) beta(t)T
 =T.                                                    (CAN7)
```

This is `(CAN4)`.  End proof.

The quantitative finite-representation matching theorem is the approximate
version: property `(T)` projects an almost-intertwiner onto this exact
finite-dimensional intertwiner space.

**Corollary 2 (finite-dimensional fixed spaces).**  Let

```text
rho:G->U(V)                                             (CAN8)
```

be a finite-dimensional unitary representation.  Under `(CAN1)`,

```text
rho(t) Fix_Gamma(rho)=Fix_Gamma(rho).                  (CAN9)
```

Consequently every `h` in `(CAN2)` acts identically on
`Fix_Gamma(rho)`.

### Proof

Conjugating the fixed-space equations gives

```text
rho(t) Fix_Gamma(rho)=Fix_(t Gamma t^(-1))(rho).       (CAN10)
```

The subgroup inclusion `(CAN1)` gives

```text
Fix_Gamma(rho)<=Fix_(t Gamma t^(-1))(rho).             (CAN11)
```

The two spaces in `(CAN11)` have the same finite dimension by `(CAN10)`.
Hence equality holds, proving `(CAN9)`.

If `xi in Fix_Gamma(rho)`, then `(CAN9)` gives
`rho(t)xi in Fix_Gamma(rho)`.  Therefore

```text
rho(h)xi
 =rho(t)^* rho(gamma) rho(t)xi
 =rho(t)^*rho(t)xi
 =xi.                                                  (CAN12)
```

End proof.

This also follows from Lemma 1 by taking `rho_1` to be the trivial
one-dimensional representation.

## 3. Almost-periodic bicommutant theorem

**Theorem 3.**  Every almost-periodic unitary representation satisfies
`(CAN2a)`.

### Proof

Write the representation space as an orthogonal direct sum of
finite-dimensional `G`-invariant spaces `V_j`, and let `p_j` be the block
projections.  If `T in pi(Gamma)'`, then

```text
T_(ij)=p_i T p_j:V_j->V_i                              (CAN13)
```

intertwines the two finite-dimensional restrictions to `Gamma`.  Lemma 1
says it intertwines `h`.  Therefore every matrix block of
`pi(h)T-T pi(h)` is zero.  Since the `p_j` sum strongly to one,
`pi(h)T=T pi(h)`.  End proof.

This is the exact noncommutative exclusion needed by the relative-
bicommutant endpoint, not only a fixed-vector statement.

## 4. Compact-action theorem

Recall that a pmp action

```text
G curvearrowright (X,mu)                               (CAN14)
```

is compact when its Koopman representation on `L^2(X)` is a Hilbert direct
sum of finite-dimensional `G`-invariant subspaces.

**Theorem 4 (compact anchor no-go).**  Every compact action `(CAN14)`
satisfies `(CAN3)`.  Equivalently,

```text
L^infinity(X)^Gamma subset L^infinity(X)^h.           (CAN16)
```

### Proof

Write the Koopman representation as

```text
L^2(X)=directSum_j V_j,                                (CAN15)
```

where every `V_j` is finite dimensional and `G`-invariant.  Orthogonal
projection onto `V_j` commutes with the `G`-action.  Hence if
`f in L^2(X)^Gamma`, every component `f_j` belongs to
`Fix_Gamma(V_j)`.  Lemma 1 gives `rho(h)f_j=f_j` for every `j`.  Summing
orthogonally yields `rho(h)f=f`, which is `(CAN3)`.

Intersecting with `L^infinity(X)` gives `(CAN16)`.  End proof.

In the crossed product `M=L^infinity(X) crossed G`, a classical relative
commutant witness from the fixed-point algebra would be a unitary

```text
v in L^infinity(X)^Gamma                               (CAN17)
```

with `[v,u_h]!=1`.  Equation `(CAN16)` says that no such unitary exists for
a compact action.

## 5. Weak compactness and property `(T)`

Ioana records the following implication.  If an ergodic pmp action of a
property-`(T)` group is weakly compact, take the positive `L^1(X times X)`
vectors in the definition of weak compactness and pass to their square
roots in `L^2(X times X)`.  They are almost invariant for the diagonal
Koopman representation.  Property `(T)` replaces them by invariant unit
vectors.  Squaring again gives invariant positive `L^1` vectors still
concentrating on the diagonal.  Ioana's compactness criterion then shows
that the action is compact.

Combining this observation with Theorem 4 gives:

**Corollary 5 (weakly compact anchor no-go).**  Assume in addition that
`G` has property `(T)`.  If an ergodic pmp action of `G` is weakly compact,
then every `Gamma`-invariant measurable function is fixed by `h`.

For the three-tag Kun--Thom pair both `Gamma` and `G` have property `(T)`,
so Corollary 5 applies directly.

## 6. Scope for the FALSE program

The relative-bicommutant endpoint says that a CE pmp action would finish
FALSE if it had a `Gamma`-fixed function moved by `h`.  Theorem 4 and
Corollary 5 show that such an action cannot come from any of the most rigid
finite-approximation classes:

1. it cannot be profinite;
2. it cannot be compact;
3. it cannot even be weakly compact when the ambient group has property
   `(T)`; and
4. by weak-compactness invariance, it cannot be orbit equivalent to a
   compact action.

The remaining classical target, if it exists, is therefore a
Connes-embeddable but non-weakly-compact action with a nontrivial relative
`Gamma`-invariant factor.  The noncommutative alternative is a CE finite
algebra `M` in which

```text
pi(Gamma)' intersect M not contained in pi(h)' intersect M. (CAN18)
```

This is a sharper boundary than merely asking for a CE action or a CE
representation of `G`.

## Reference

Adrian Ioana, *Cocycle superrigidity for profinite actions of property (T)
groups*, arXiv:0805.2998, Section 6, especially Proposition 6.3 and the
property-`(T)` argument in Remark 6.4.
