# A router--detector construction of a torsion-free finitely presented non-MF group

**Date:** 2026-08-22

This artifact is the explicit Fournier--Facio instance of the more general
`research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md`.
The master theorem accepts an arbitrary op-to-HS killed subgroup and uses no
compression structure in its detector hypothesis.

## Result

There is a nontrivial finitely presented torsion-free property-`(T)` group
`G` such that every homomorphism from `G` to the unitary group of every
operator-norm matrix corona is trivial.  Equivalently,

```text
normMFResidual G = G.
```

In particular `G` is not MF.  This is the route compiled by Cairn as
`torsion-free-non-mf-from-normal-kazhdan-defect`; its stronger full-residual
form is `defect-saturation-full-mf-radical`.

The proof has two independent modules.

1. A small-cancellation **router** makes a prescribed simple subgroup
   normally generate the final quotient.
2. A normal Kazhdan **detector** turns any surviving operator-norm corona
   image into a self-normalized tracial corner, where the usual
   Hilbert--Schmidt compression calculation kills it.

No finite central subgroup, central involution, negative spectral cut,
Clifford survival representation, Hilbert-hotel construction, or Leavitt
algebra is used.  The output group is torsion-free.

## 1. MF convention

For dimensions `d_n`, let

```text
Q_op = (product_n M_(d_n)(C)) / (operator-norm-null sequences).
```

A countable group is operator MF if it embeds into `U(Q_op)` for some
dimension sequence.  The construction below proves the stronger assertion
that every homomorphism `G -> U(Q_op)` is the trivial homomorphism.

## 2. The analytic detector

Let `E` be countable.  A compression core consists of an infinite
property-`(T)` subgroup `Gamma <= E` and elements `t,c in E` such that

```text
t Gamma t^(-1) <= Gamma,
[c,Gamma] = 1.
```

Put `c_hat=tct^(-1)` and

```text
D(E;Gamma,t,c)
  = normalClosure_E({[c_hat,gamma] : gamma in Gamma}).
```

The machine-checked normal-Kazhdan detector theorem says:

> If `K triangleleft E` is nontrivial, has property `(T)`, and satisfies
> `K <= D(E;Gamma,t,c)`, then every norm-matrix-corona homomorphism out of
> `E` kills `K` elementwise.  Hence `E` is not MF.

The two endpoint declarations are

```text
KazhdanCompressionCore.not_isWeakMF_of_normalKazhdan_le_defect
KazhdanCompressionCore.normalKazhdan_le_normMFResidual.
```

They live in
`GroupApproximation/Sofic/NormalKazhdanCompressionObstruction.lean` and
`GroupApproximation/Sofic/NormalKazhdanMFRadical.lean`; the reader-facing
proof route is `normal-kazhdan-defect-non-mf-proof`.

### Why this detects an operator-norm witness

Suppose some `k in K` survives in a norm-corona representation.  Coordinate
unitary lifts need not have positive normalized-Hilbert--Schmidt mass: the
moving part could have rank `o(d_n)`.  Property `(T)` of `K` supplies the
fixed-space projection in the coordinate action.  Its orthogonal complement
is nonzero along a subsequence because an element of `K` survives in operator
norm.

Normality is the crucial ambient hypothesis.  Conjugation by every element of
`E` permutes `K`, so the `K`-fixed space and its moving complement are
ambient-invariant.  After the standard perturbation and polar correction, the
moving corners therefore carry an asymptotic representation of all of `E`,
not merely of `K`.  Normalize trace by the rank of each moving corner.  The
Kazhdan inequality now forces a fixed element of a Kazhdan set of `K` to have
positive normalized-Hilbert--Schmidt displacement.

On the same corner the one-sided compression calculation transports the
centralizer of `Gamma`: since `c` centralizes `Gamma` and
`t Gamma t^(-1) <= Gamma`, every `[tct^(-1),gamma]` is tracially invisible.
The tracially invisible elements form a normal subgroup, so the whole defect
`D` is killed.  This contradicts `K <= D` and the Kazhdan lower bound.

Thus the fixed-space projection of a normal Kazhdan subgroup replaces the
finite spectral projection used by central-sign arguments.  It self-normalizes
the trace and prevents operator-norm separation from hiding on a
vanishing-density sector.

## 3. The torsion-free group-theoretic source

Use the source data recorded by `fournier-facio-torsion-free-skeleton`:

- a finitely presented torsion-free property-`(T)` group `P` containing
  `P_1 x P_2 x S`, with `P_i` isomorphic to `P` and `S` an infinite finitely
  presented nonabelian simple torsion-free group;
- a torsion-free hyperbolic property-`(T)` group `H`;
- the double HNN extension

  ```text
  E = <P,u_1,u_2 | u_i P u_i^(-1)=P_i>.
  ```

The group `E` is finitely presented, torsion-free, and acylindrically
hyperbolic.  Let

```text
N = normalClosure_E(S).
```

It is an infinite normal subgroup of `E`.

## 4. Route every generator through `N`

The established routing theorem
`defect-normally-generates-torsion-free-quotient` modifies Hull's
finitely-generated common-quotient construction by choosing its
small-cancellation reservoir inside `N`.

An infinite normal subgroup of a torsion-free acylindrically hyperbolic group
is `s`-normal, hence acts non-elementarily by Osin's theorem.  The finite
radical is trivial, so `N` is suitable in Hull's sense.  Hull's machinery
therefore supplies noncommensurable infinite-order reservoir elements
`h_1,h_2 in N`.

For a finite generating set, Hull's relators have the routing shape

```text
x = W_x(h_1,h_2).
```

Every generator of the common quotient is consequently in the image of `N`.
After protecting a chosen `1 != s in S`, the output maps are

```text
E ->> G <<- H
```

with

```text
pi(s) != 1,
pi(N) = G.
```

Hull's finite-set injectivity and torsion clauses give survival and
torsion-freeness; the finitely generated branch uses finitely many relators,
so the quotient is finitely presented.  Property `(T)` passes to `G` from the
surjection `H ->> G`.  This last provenance matters: the HNN source `E` is
not being asserted to have property `(T)`.

Put `S'=pi(S)`.  Simplicity of `S` and survival of `s` imply that `pi|_S` is
injective.  Thus `S'` is again infinite, nonabelian, simple, and torsion-free,
and the routing identity becomes

```text
G = normalClosure_G(S').
```

The complete source audit is
`notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md`; Cairn records it as
`defect-normally-generates-torsion-free-quotient-proof`.

## 5. Manufacture the compression mark without torsion

Set

```text
Gamma = pi(P),
t = pi(u_1).
```

The quotient relation gives `t Gamma t^(-1) <= Gamma`.  Since
`[P_1,S]=1`, the subgroup

```text
J = t^(-1) S' t
```

centralizes `Gamma`.  For the protected `s'=pi(s)`, define

```text
c = t^(-1) s' t.
```

Then

```text
[c,Gamma] = 1,
t c t^(-1) = s' in S' <= Gamma.
```

So `(Gamma,t,c)` is a compression core.  No finite-order element is used.

## 6. The compiler identity: the defect is the whole group

The compression defect is

```text
D = normalClosure_G({[s',gamma] : gamma in Gamma}).
```

Because `S'` is nonabelian simple, its centre is trivial.  The protected
element `s'` is nontrivial, so there is `x in S'` with `[s',x] != 1`.  Since
`S' <= Gamma`,

```text
1 != [s',x] in D cap S'.
```

The intersection `D cap S'` is normal in `S'`; simplicity gives `S' <= D`.
But `D` is normal in `G`, and the router gave
`normalClosure_G(S')=G`.  Therefore

```text
D = G.
```

This is the algebraic compiler step: one authenticated nonzero compression
challenge propagates through the routed normal closure to every ambient
generator.

The downstream algebra is kernel-checked in
`GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`.  In particular:

```text
FournierFacioDefectData.simpleSubgroup_le_defectNormal
DefectRoutingData.mapped_defectNormal_eq_top.
```

The acylindrical-small-cancellation existence of the routing data remains the
explicit paper-level trust boundary; it is not encoded as a Lean axiom.

## 7. Full MF residual and non-MF

Apply the normal-Kazhdan detector with ambient group `E=G` and normal Kazhdan
subgroup `K=G`.  The hypotheses are immediate:

```text
G triangleleft G,
G != 1,
G has property (T),
G <= D = G.
```

Every homomorphism from `G` to every norm matrix corona therefore kills all
of `G`.  Hence

```text
normMFResidual G = G,
```

and `G` is not MF.  The Lean endpoints include

```text
DefectRoutingData.coronaMFResidual_eq_top
DefectRoutingData.cdeMFResidual_eq_top
DefectRoutingData.normMFResidual_eq_top
DefectRoutingData.coronaRepresentation_eq_one
DefectRoutingData.cdeCoronaRepresentation_eq_one
DefectRoutingData.not_isOperatorMF
DefectRoutingData.not_isCDEOperatorMF.
```

Surjective functoriality of the full residual also shows that every
nontrivial quotient of `G` has full MF residual and is non-MF.

## 8. Asymptotic-representation form

If `phi_n : G -> U(d_n)` is an operator-norm asymptotic homomorphism, then

```text
Theta(g) = [(phi_n(g))]
```

defines a homomorphism into the cofinite norm matrix corona.  Total corona
triviality gives `Theta(g)=1` for every fixed `g`, which unwinds to

```text
||phi_n(g)-1||_op -> 0.
```

Thus every operator-norm asymptotic representation is pointwise
asymptotically trivial.  Cairn records this consequence as
`fournier-facio-asymptotic-representations-trivial`, and hence also records
the resulting (degenerate) matricial stability.

## 9. Structural comparison and compiler interpretation

The central-sign route obtains its self-normalized corner from the negative
spectral projection of a finite-order central element and proves survival by
a Clifford representation.  The present route instead uses the moving-space
projection of an infinite normal Kazhdan subgroup.  Normality makes the
corner ambient-invariant; property `(T)` gives the lower bound; no marked
finite spectrum appears.

The construction can be read as a finite compiler:

```text
route -> authenticate -> challenge -> propagate -> detect -> HS reject.
```

- **Route:** rewrite every final generator as a word in a reservoir inside
  `normalClosure(S)`.
- **Authenticate:** protect one nontrivial element of `S`; simplicity upgrades
  its survival to injectivity on all of `S`.
- **Challenge:** conjugate that state element out to a centralizer and back,
  producing `[s',gamma]`.
- **Propagate:** a single nonzero challenge captures `S'`, whose normal
  closure is all of `G`.
- **Detect:** the normal-Kazhdan fixed-space projection isolates and
  self-normalizes any operator-norm moving sector.
- **Reject:** Hilbert--Schmidt compression kills the whole defect, now equal
  to the whole group.

This does not solve the open reverse-Kleene quantitative compiler.  It avoids
that problem by making a local authenticated defect normally generate the
entire output before finite-dimensional approximation begins.

## 10. Cairn dependency map

The primary route is

```text
normal-kazhdan-defect-non-mf
AND fournier-facio-torsion-free-skeleton
AND defect-normally-generates-torsion-free-quotient
  => torsion-free-finitely-presented-non-mf
```

under the route id
`torsion-free-non-mf-from-normal-kazhdan-defect`.

The same three premises establish the stronger node
`defect-saturation-full-mf-radical` through
`defect-saturation-full-mf-radical-proof`.  From there Cairn also reaches:

- `torsion-free-finitely-presented-non-mf` by the cheap full-residual route;
- `fournier-facio-asymptotic-representations-trivial` by interpreting an
  asymptotic representation in the cofinite corona;
- `fournier-facio-group-matricially-stable` by correcting every asymptotic
  representation with the trivial representations.

The proof therefore lands at the strongest reusable invariant already
present in the graph, rather than only at the existential non-MF root.
