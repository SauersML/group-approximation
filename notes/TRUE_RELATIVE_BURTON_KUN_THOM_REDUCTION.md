# A relative hyperlinear-to-sofic gate for the Kun--Thom wreath product

Date: 2026-08-13

## 1. Purpose

Let `Gamma<G` be the explicit Kun--Thom pair and put

```text
X=G/Gamma,
A=direct_sum_X C_2,
W=A semidirect G.                                      (RBK1)
```

Kun--Thom prove that `W` is nonsofic.  This note isolates a matrix theorem
which would upgrade that result to nonhyperlinearity.  Unlike a general
tracial commutant-lifting conjecture, the theorem only concerns the normalizer
of the locally finite abelian lamp subgroup in the canonical trace.

The reduction uses the quantitative theorem of
Burton--Chaudkhari--Juschenko--Muliarchyk: a sufficiently accurate
hyperlinear approximation of an amenable group can, on a prescribed finite
set, be replaced in normalized Hilbert--Schmidt norm by a sofic-induced
approximation on the same finite-dimensional Hilbert space.

## 2. Restricting a hypothetical hyperlinear model to the lamps

Assume for contradiction that `W` is hyperlinear.  Choose trace-faithful
asymptotic representations

```text
theta_n:W -> U(d_n).                                    (RBK2)
```

Thus, for fixed `u,v in W`,

```text
||theta_n(uv)-theta_n(u)theta_n(v)||_(2,d_n) -> 0,       (RBK3)
tr_(d_n)(theta_n(u)) -> 0,                 u!=1.         (RBK4)
```

The restriction to `A` is a hyperlinear approximation of the amenable group
`A`.  Apply the quantitative amenable hyperlinear-to-sofic theorem on an
increasing sequence of finite lamp sets and diagonalize.  After passing to a
subsequence there are maps

```text
sigma_n:A -> Sym(V_n),             |V_n|=d_n,            (RBK5)
```

whose permutation matrices, still denoted `sigma_n(a)`, satisfy

```text
||sigma_n(a)-theta_n(a)||_(2,d_n) -> 0                  (RBK6)
```

for every fixed `a in A`, and `(sigma_n)` is a sofic approximation of `A`.
If the same-dimension formulation is replaced by an asymptotically equal
dimension formulation, all statements below are unchanged after the usual
`o(d_n)` padding.

Here `V_n` is an orthonormal basis of the abstract Hilbert space selected by
the Burton--Chaudkhari--Juschenko--Muliarchyk construction.  The assertion is
not closeness to permutation matrices in a previously fixed coordinate basis;
that coordinate-dependent strengthening would fail after a generic unitary
conjugation.  Express every `theta_n(g)`, including the quotient unitaries
below, in the one basis selected by the theorem.  This simultaneous change of
basis preserves `(RBK3)--(RBK4)` and every covariance and coherence estimate
used below.

Put

```text
U_(g,n)=theta_n(g),                 g in G.              (RBK7)
```

The original semidirect-product covariance and `(RBK6)` give, for every
fixed `g in G` and `a in A`,

```text
||U_(g,n) sigma_n(a) U_(g,n)^*
       -sigma_n(g a g^(-1))||_(2,d_n) -> 0.             (RBK8)
```

Indeed the left side is at most the sum of

```text
||sigma_n(a)-theta_n(a)||_2,
||theta_n(g)theta_n(a)theta_n(g)^*
       -theta_n(gag^(-1))||_2,
||theta_n(gag^(-1))-sigma_n(gag^(-1))||_2,              (RBK9)
```

and every term tends to zero.  Similarly,

```text
||U_(g,n)U_(h,n)-U_(gh,n)||_(2,d_n) ->0.                (RBK10)
```

Thus hyperlinearity of `W` produces a genuine permutation model of the
lamp subgroup together with coherent **unitary** approximate normalizers
implementing the `G`-action.

## 3. The exact missing normalizer-transfer theorem

The following special statement would finish the universal-hyperlinearity
problem negatively.

**Equivariant normalizer transfer for `(A,G)`.**  Suppose `(sigma_n,U_n)`
satisfies `(RBK5)`, `(RBK8)`, `(RBK10)`, the canonical trace-separation
conditions inherited from `(RBK4)`, and arises from a trace-faithful
hyperlinear approximation of `A semidirect G`.  Then, after `o(d_n)`
padding, there are permutations

```text
P_(g,n) in Sym(V'_n),                                  (RBK11)
```

and sofic lamp approximations `sigma'_n` essentially equivalent to
`sigma_n` such that, for every fixed `g,h in G` and `a in A`,

```text
d_H(P_(g,n)P_(h,n),P_(gh,n)) ->0,                      (RBK12)
d_H(P_(g,n)sigma'_n(a)P_(g,n)^(-1),
       sigma'_n(gag^(-1))) ->0,                        (RBK13)
```

and the quotient permutations are asymptotically free on nonidentity
elements of `G`.

The asymptotic freeness clause can equivalently be supplied by tensoring
with a fixed sofic approximation of the residually finite group `G`, once
`(RBK12)--(RBK13)` have been obtained.

**Theorem 1 (conditional nonhyperlinearity).**  Equivariant normalizer
transfer for the explicit Kun--Thom action implies that `W` is
nonhyperlinear.

**Proof.**  If `W` were hyperlinear, Section 2 would produce
`(sigma_n,U_n)`.  Apply normalizer transfer.  Define

```text
Phi_n(a g)=sigma'_n(a)P_(g,n).                          (RBK14)
```

Equations `(RBK12)--(RBK13)` and the sofic multiplication law for
`sigma'_n` show that `(Phi_n)` is asymptotically multiplicative.  Lamp
freeness separates elements with `a!=1`, and quotient freeness separates
elements with `g!=1`.  Hence `(Phi_n)` is a sofic approximation of `W`,
contradicting the Kun--Thom theorem.  End proof.

This proves the contrapositive formulation

```text
W hyperlinear
  ==> equivariant normalizer transfer fails for its canonical lamp model.
                                                               (RBK15)
```

Accordingly, proving the displayed transfer theorem produces an explicit
nonhyperlinear group, not merely a hyperlinear nonsofic group.

## 4. Why ordinary amenable conversion is not enough

The Burton--Chaudkhari--Juschenko--Muliarchyk theorem proves `(RBK5)--(RBK6)`
but does not include the normalizing family `U_(g,n)`.  Applying it
separately after conjugation loses the coherence in `(RBK10)`.

There are two concrete obstructions to a formal extension.

1. For a finite elementary abelian lamp group, unitary equivalence of two
   permutation representations need not imply isomorphism of the underlying
   finite sets.  The map from the Burnside semiring to the complex
   representation semiring has nontrivial relations once the rank grows.
   Thus an individual unitary intertwiner cannot simply be rounded to a
   permutation intertwiner.
2. On a finite lamp patch, the maps `x |-> g x` are only partial
   permutations of the patch.  Extending each one separately is easy, but
   choosing the extensions so that all group products agree on almost every
   point is precisely the global action-soficity issue.  The Kun--Thom coset
   action has no profinite or Folner exhaustion which supplies this
   coherence automatically.

The canonical trace does remove part of the first obstruction.  On every
fixed finite lamp subgroup `B< A`, `(RBK4)` makes the restriction
asymptotically a multiple of the regular character of `B`; after negligible
padding, the permutation model is a union of free `B`-orbits.  Therefore the
remaining difficulty is not arbitrary Gassmann equivalence on one fixed
`B`.  It is coherent passage through the increasing, non-invariant lamp
patches while retaining `(RBK10)`.

There is an exact quantization which shows that a Folner-style patch argument
cannot soften this difficulty.  For finite `Y,Z subset X`, put

```text
B_Y=direct_sum_Y C_2 <= A.
```

Then

```text
B_Y intersect B_Z=B_(Y intersect Z),
[B_Y:B_Y intersect B_Z]=2^|Y-Z|.                       (RBK16)
```

Equivalently, in the regular representation of `B_(Y union Z)`, the
projections onto the `B_Y`- and `B_Z`-fixed spaces have intersection ratios
quantized in powers of `1/2`.  In particular,

```text
|B_Y intersect B_(gY)|/|B_Y| ->1
       ==> gY=Y eventually.                             (RBK17)
```

There is no sequence of merely *almost* invariant uniform finite lamp
groups: the first missing coordinate already costs one half of the regular
character space.  This is stronger than the usual boundary-rank estimate,
but it does not itself give a contradiction.  The finite subgroup `B_Y`
obtained while approximating a fixed finite window need not be preserved by
the quotient matrices outside that window.  Extracting a single finite
`Y` on which all relevant quotient generators act coherently is exactly the
normalizer-transfer statement.

This identifies the smallest live strengthening of the amenable conversion
theorem:

> prove its random-basis construction relative to a finite family of
> coherent ambient normalizers, for the regular finite-subgroup sectors of
> `direct_sum_(G/Gamma) C_2`.

That statement is narrower than Alekseev--Thom Open Problem 6.2: it does not
ask to recover the full commutant of an arbitrary Kazhdan matrix
representation.  It asks only for permutation spatialization of one locally
finite abelian normal subgroup in the canonical group trace.

## 5. Relation to the Clifford phase route

The commuting-lamp group `W` and the Clifford crossed product carry the two
sides of the same Kun--Thom defect.  In the Clifford model the second
commutator is the scalar `-1`; in `W` the corresponding two lamps commute.
The present reduction attacks nonhyperlinearity of `W` by proving that a
tracial matrix model would have to remember the underlying finite lamp
sets.  The Clifford route instead asks for a tracial matrix model in which
the local anticommutation survives.  They are complementary:

```text
relative normalizer transfer  ==> W is nonhyperlinear,
Clifford crossed product CE   ==> a hyperlinear nonsofic image exists.
```

The first implication answers the universal-hyperlinearity problem; the
second answers the hyperlinear-versus-sofic problem.

## References

- G. Kun and A. Thom, *Nonsofic wreath products of residually finite groups*, arXiv:2608.06222v1.
- P. Burton, M. Chaudkhari, K. Juschenko, and K. Muliarchyk, *Hyperlinear approximations to amenable groups come from sofic approximations*, arXiv:2311.09202v2.
- V. Alekseev and A. Thom, *Centralizers of sofic approximations of Kazhdan groups*, arXiv:2608.05362v1, Open Problem 6.2.
