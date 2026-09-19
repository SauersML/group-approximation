---
rg: 2
id: agent-groupfactor-bcs-reynolds-free-holonomy-trichotomy
kind: claim
title: Free, finite-action, and HNN sign carriers do not softly promote a BCS trace to a group-factor corner
distinct_from:
  unitary-corner-compressions-force-reduction: that treats compression of a unitary by an arbitrary projection; this treats projection-valued payloads compressed by a finite Reynolds carrier and computes the free-product and crossed-product relative commutants.
  finite-holonomy-crossed-products-do-not-promote-canonical-trace: that proves Connes-embeddability equivalence for an arbitrary finite crossed product; this identifies the Reynolds corner itself with the fixed-point algebra and contrasts it with a freely adjoined sign and a genuine HNN letter.
  involution-hecke-corner-has-no-proper-literal-projections: that classifies a literal compression qgq in a canonical group algebra; this starts from an arbitrary payload projection and proves the exact free/action/HNN carrier trichotomy, together with the nonregular Halmos character formula.
---

**ESTABLISHED OBSTRUCTION.**  Let `(M,tau)` be a finite tracial von
Neumann algebra and let `K` be a nontrivial finite group.  Write

```text
e_K=|K|^(-1) sum_(k in K) u_k.                         (RFH1)
```

The two standard ways of adjoining `K` have opposite, but equally terminal,
behaviour.

## 1. A free sign scalarizes every payload projection

In the reduced free product

```text
N=(M,tau) * (L(K),tau_K),                              (RFH2)
```

if `P in M` is a projection and `e_K P e_K` is a projection in the corner
`e_K N e_K`, then

```text
P=0 or P=1.                                            (RFH3)
```

Indeed, for any two projections `e,P`, the compression `ePe` is a projection
if and only if `eP=Pe`: from

```text
ePe-(ePe)^2=eP(1-e)Pe=((1-e)Pe)^*((1-e)Pe),            (RFH4)
```

vanishing gives `(1-e)Pe=0`, and adjoints give `eP(1-e)=0`.

It remains to compute the relative commutant.  Put

```text
e_K=|K|^(-1)1+e_0,       e_0 in L^2(L(K)) minus C1,
```

where `e_0!=0`.  If `x in M`, replace it by `x-tau(x)1`.  Reduced-word
orthogonality puts

```text
x e_0 in L^2(M)^0 tensor L^2(L(K))^0,
e_0 x in L^2(L(K))^0 tensor L^2(M)^0.                 (RFH5)
```

These subspaces are orthogonal, and

```text
||x e_0||_2=||e_0 x||_2=||x||_2 ||e_0||_2.            (RFH6)
```

Thus `[x,e_K]=0` forces `x=0`, proving

```text
M intersect {e_K}'=C1.                                 (RFH7)
```

Equations `(RFH4)` and `(RFH7)` prove `(RFH3)`.  The same proof works with
any non-scalar projection of `L(K)` in place of `e_K`.  In particular, if a
fresh involution `J` is freely adjoined, neither `(1+J)/2` nor `(1-J)/2`
can directly compress a nontrivial BCS projection to a projection.  A whole
context PVM therefore collapses to a scalar assignment before any overlap or
predicate holonomy is tested.

## 2. A finite acting sign returns exactly the fixed-point algebra

Let `alpha:K -> Aut(M,tau)` be a trace-preserving action, put

```text
N=M rtimes_alpha K,
```

and use the same `e_K` in `N`.  For a projection `P in M`,

```text
e_K P e_K is a projection in e_K N e_K
 iff P in M^K.                                         (RFH8)
```

The first equivalence in `(RFH4)` again says that compression is a
projection exactly when `[P,e_K]=0`.  Uniqueness of crossed-product Fourier
coefficients gives

```text
P e_K=e_K P
 iff alpha_k(P)=P for every k in K.                    (RFH9)
```

Moreover the map

```text
M^K -> e_K N e_K,       x |-> x e_K                   (RFH10)
```

is a normal star isomorphism.  Surjectivity follows from

```text
e_K x e_K=E_(M^K)(x)e_K,       e_K u_k=e_K,            (RFH11)
```

first on the algebraic crossed product and then by normality.  Finally,

```text
tau_N(e_K)=1/|K|,
tau_(e_K N e_K)(x e_K)
 =tau_N(xe_K)/tau_N(e_K)=tau(x).                       (RFH12)
```

Thus finite holonomy does not promote or regularize the payload trace: its
Reynolds corner is precisely the fixed-point algebra with the old trace.  If
`M=L(H)` and the action comes from automorphisms of `H`, then
`N=L(H rtimes K)`.  A no-CE BCS model in this Reynolds corner already lies
trace preservingly in `L(H)` by `(RFH10)`, so `H` is already nonhyperlinear.
For the trivial action (a genuinely central involution), `(RFH10)` is simply

```text
((1-J)/2)L(H times C_2)((1-J)/2) ~= L(H).              (RFH13)
```

Centralizing the sign is therefore exactly circular.

## 3. A genuine HNN letter has no positive Reynolds carrier

Let `G` be a genuine HNN extension with stable letter `t`.  Its height map
sends `t` to `1 in Z`, so `t` has infinite order and

```text
tau_G(t^n)=0                 (n!=0).                   (RFH14)
```

Hence the spectral distribution of `lambda_t` is Haar measure on the circle
and its eigenvalue-one spectral projection is zero.  Consequently

```text
q lambda_t=q   or   lambda_t q=q,
q=q^*=q^2 in L(G),
implies q=0.                                             (RFH15)
```

There is therefore no positive-trace HNN carrier on which the stable letter
can be replaced by the identity in order to turn conjugacy of two context
copies into literal equality.  Adding `t^m=1` destroys the height map and is
not a genuine HNN extension.  The two soft endpoints are then exactly the
ones above: a freely adjoined `C_m` gives `(RFH3)`, while a finite action on
the whole base gives `(RFH10)`.  An intermediate finite-order quotient with
partial conjugacy relations is not ruled out by this trichotomy, but those
quotient relations themselves must be load-bearing; amenable-edge
Bass--Serre permanence excludes all versions assembled from hyperlinear
pieces along amenable interfaces.

## 4. The literal Halmos attempt exposes the trace failure immediately

For a projection `P in M`, the standard two-by-two construction is

```text
h=[[1,0],[0,-1]],
r_P=[[P,1-P],[1-P,-P]],
q=(1+h)/2.                                              (RFH16)
```

Both `h` and `r_P` are involutions and

```text
q r_P q=P q,
(h r_P)^2=(2P-1)I_2,
(h r_P)^4=I_2.                                         (RFH17)
```

With the normalized matrix trace,

```text
(tr_2 tensor tau)(h r_P)=tau(P).                       (RFH18)
```

If `0<P<1`, then `h r_P!=1` while `(RFH18)` is strictly positive.  Thus the
representation of the group generated by the two Halmos reflections is not
the canonical regular representation.  Also

```text
[h,r_P]=0 iff P=1,                                     (RFH19)
```

because centrality kills the off-diagonal entry `1-P`.  So making the
Halmos grading into the authenticated central sign collapses its proper
projection, while leaving it noncentral retains exactly the nonregular
character that the group-factor route must remove.

Free Haar tags can annihilate the coefficient `(RFH18)`, but exact recovery
then requires a tag-cancelling word.  The cancellation kernel criterion of
`haar-tag-cancellation-retention-is-group-realizability` says that such a
kernel either erases the payload or is already a regular group-factor host
for the retained payload.  Hence tags do not furnish a fourth soft case.

## Consequence for the fixed non-RU BCS

The no-CE BCS has no classical assignment, so in every tracial model at
least one Boolean spectral projection is proper.  For that projection the
free-sign model fails by `(RFH3)`, the Halmos model fails canonicality by
`(RFH18)`, a central/finite-action sign merely returns a trace-preserving
subalgebra of the original payload by `(RFH10)--(RFH13)`, and an infinite
HNN letter has no nonzero invariant carrier by `(RFH15)`.

The exact remaining obstruction is therefore unchanged but narrower: one
must construct genuinely non-Cartan, non-Reynolds elements in a canonical
group-factor corner, or a finite-order partial-conjugacy quotient whose own
relations are already the first nonhyperlinear step.  Ordinary free
adjoining, finite holonomy, centralization, and genuine HNN averaging cannot
perform the trace promotion.
