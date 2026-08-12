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

Then every compact probability-measure-preserving action of `G` has the
following rigidity:

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

## 2. Finite-dimensional fixed-space equality

The key point uses only finite dimensionality; property `(T)` is not needed
until the later passage from weakly compact to compact actions.

**Lemma 1.**  Let

```text
rho:G->U(V)                                             (CAN4)
```

be a finite-dimensional unitary representation.  Under `(CAN1)`,

```text
rho(t) Fix_Gamma(rho)=Fix_Gamma(rho).                  (CAN5)
```

Consequently every `h` in `(CAN2)` acts identically on
`Fix_Gamma(rho)`.

### Proof

Conjugating the fixed-space equations gives

```text
rho(t) Fix_Gamma(rho)=Fix_(t Gamma t^(-1))(rho).       (CAN6)
```

The subgroup inclusion `(CAN1)` gives

```text
Fix_Gamma(rho)<=Fix_(t Gamma t^(-1))(rho).             (CAN7)
```

The two spaces in `(CAN7)` have the same finite dimension by `(CAN6)`.
Hence equality holds, proving `(CAN5)`.

If `xi in Fix_Gamma(rho)`, then `(CAN5)` gives
`rho(t)xi in Fix_Gamma(rho)`.  Therefore

```text
rho(h)xi
 =rho(t)^* rho(gamma) rho(t)xi
 =rho(t)^*rho(t)xi
 =xi.                                                  (CAN8)
```

End proof.

The finite-dimensional matching theorem is a two-representation version
of this argument.  Lemma 1 is the fixed-vector form needed for actions.

## 3. Compact-action theorem

Recall that a pmp action

```text
G curvearrowright (X,mu)                               (CAN9)
```

is compact when its Koopman representation on `L^2(X)` is a Hilbert direct
sum of finite-dimensional `G`-invariant subspaces.

**Theorem 2 (compact anchor no-go).**  Every compact action `(CAN9)`
satisfies `(CAN3)`.  Equivalently,

```text
L^infinity(X)^Gamma subset L^infinity(X)^h.           (CAN10)
```

### Proof

Write the Koopman representation as

```text
L^2(X)=directSum_j V_j,                                (CAN11)
```

where every `V_j` is finite dimensional and `G`-invariant.  Orthogonal
projection onto `V_j` commutes with the `G`-action.  Hence if
`f in L^2(X)^Gamma`, every component `f_j` belongs to
`Fix_Gamma(V_j)`.  Lemma 1 gives `rho(h)f_j=f_j` for every `j`.  Summing
orthogonally yields `rho(h)f=f`, which is `(CAN3)`.

Intersecting with `L^infinity(X)` gives `(CAN10)`.  End proof.

In the crossed product `M=L^infinity(X) crossed G`, a classical relative
commutant witness from the fixed-point algebra would be a unitary

```text
v in L^infinity(X)^Gamma                               (CAN12)
```

with `[v,u_h]!=1`.  Equation `(CAN10)` says that no such unitary exists for
a compact action.

## 4. Weak compactness and property `(T)`

Ioana records the following implication.  If an ergodic pmp action of a
property-`(T)` group is weakly compact, take the positive `L^1(X times X)`
vectors in the definition of weak compactness and pass to their square
roots in `L^2(X times X)`.  They are almost invariant for the diagonal
Koopman representation.  Property `(T)` replaces them by invariant unit
vectors.  Squaring again gives invariant positive `L^1` vectors still
concentrating on the diagonal.  Ioana's compactness criterion then shows
that the action is compact.

Combining this observation with Theorem 2 gives:

**Corollary 3 (weakly compact anchor no-go).**  Assume in addition that
`G` has property `(T)`.  If an ergodic pmp action of `G` is weakly compact,
then every `Gamma`-invariant measurable function is fixed by `h`.

For the three-tag Kun--Thom pair both `Gamma` and `G` have property `(T)`,
so Corollary 3 applies directly.

## 5. Scope for the FALSE program

The relative-bicommutant endpoint says that a CE pmp action would finish
FALSE if it had a `Gamma`-fixed function moved by `h`.  Theorem 2 and
Corollary 3 show that such an action cannot come from any of the most rigid
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
pi(Gamma)' intersect M not contained in pi(h)' intersect M. (CAN13)
```

This is a sharper boundary than merely asking for a CE action or a CE
representation of `G`.

## Reference

Adrian Ioana, *Cocycle superrigidity for profinite actions of property (T)
groups*, arXiv:0805.2998, Section 6, especially Proposition 6.3 and the
property-`(T)` argument in Remark 6.4.
