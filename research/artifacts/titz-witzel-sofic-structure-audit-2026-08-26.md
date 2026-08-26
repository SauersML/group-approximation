# Titz--Witzel soficity: structural audit and the smallest finite gate

Primary source: T. Titz Mite and S. Witzel, *Non-residually finite
`C~_2`-lattices*, arXiv:2509.05054v2, especially Sections 3--4,
Proposition 4.3 and Corollary 4.4.  The authors' verification repository
`TitzMite/NonResiduallyFinite` was inspected at its current default branch.

## What is already unconditional

For the smallest example, `K=Gamma_1^2=pi_1(Y_1^2)` is the finite residual
of `barGamma=barGamma_1^2`, with index two.  It is finitely presented,
torsion-free, infinite, simple and Kazhdan.  Dadarlat's MF-to-weak-
quasidiagonality implication and Ozawa--Thom Proposition 3.19 show that every
infinite simple Kazhdan group is non-MF.  Hence

```text
Rad_MF(K)=K
```

without any additional computation.  Only soficity remains.

## The explicit gate

Proposition 4.3 presents `barGamma` on `g1,...,g15` using 11 length-two
relations and 13 length-four relations.  Titz Mite--Witzel prove that

```text
delta_bar=g1 g6^(-1)=g1 g3,
w=delta_bar^4
```

is nontrivial and that its normal closure in `barGamma` is the index-two
subgroup `K`.  In Corollary 4.4, under `hi -> g1 gi`, the same mark is
`h3^4`.  Since `K` is simple, this nonidentity word normally generates `K`
inside `K` as well.

Soficity is invariant under finite-index passage, so `K` is sofic exactly
when `barGamma` is.  Moreover it is enough to construct approximate
permutation solutions of the 24 relators in which `w` stays a positive
Hamming distance from the identity.  Such a sequence gives a homomorphism
of `barGamma` to a metric permutation ultraproduct whose restriction to `K`
is nontrivial, hence injective by simplicity.  This makes `K` sofic; finite
extension permanence then makes `barGamma` sofic.  The converse follows
from any sofic approximation of `barGamma`.

Four length-two relations first eliminate

```text
g6=g3^(-1),  g8=g5^(-1),  g9=g7^(-1),  g14=g12^(-1).
```

The remaining length-two constraints say that
`g1,g2,g4,g10,g11,g13,g15` are involutions.  Eight of the thirteen quartic
relations then eliminate eight more variables.  Set `x=g3`, `y=g7`,
`z=g12`, and define words

```text
A=x y^(-2),                 B=z y^(-1) z,
C=y^2 x,                    D=z y^(-1) z x y^(-1),
E=y^(-1) z^2,               F=x^(-1) z^2 y^(-1) x,
S=z^(-1) x^(-1) y z^(-2),  H=z^2 y^(-1).
```

The exact Tietze substitutions are

```text
g1=A, g2=B, g3=x, g4=C, g5=D, g6=x^(-1), g7=y,
g8=D^(-1), g9=y^(-1), g10=E, g11=F, g12=z,
g13=S, g14=z^(-1), g15=H.
```

Direct free cancellation verifies that the presentation becomes

```text
<x,y,z | A^2,B^2,C^2,E^2,F^2,S^2,H^2,
         A C D B, x z C S, A E D F, D F E H, D S F E>.
```

For example, the defining quartics are solved successively as
`g1=x y^(-2)`, `g4=y^2x`, `g2=z y^(-1)z`, `g10=y^(-1)z^2`,
`g15=z^2y^(-1)`, `g13=z^(-1)x^(-1)yz^(-2)`,
`g11=x^(-1)z^2y^(-1)x`, and `g5=z y^(-1)z x y^(-1)`.
The five unused quartics become the last five relators displayed above.
Thus the computational target has three permutation variables, twelve
relator constraints, and the single separation objective

```text
d_H(y^8,1) >= c
```

for one fixed `c>0` along dimensions tending to infinity.  Precisely, the
raw substituted mark is `(x y^(-2)x)^4`; since `A y^2=x`, the relator
`A^2=1` gives `A x=y^2`.  In approximate permutation solutions,
`d_H(Ax,y^2) <= d_H(A^2,1)`, so replacing the raw mark by `y^8` changes its
Hamming distance by a quantity tending to zero.

## Why the apparent closure routes do not apply

1. **Graph of groups.**  An infinite property-`(T)` group has Serre's
   property `FA`.  A nontrivial reduced amalgam or HNN decomposition would
   give an action on its Bass--Serre tree without a global fixed point.
   Therefore `K` has no nontrivial graph-of-groups decomposition at all,
   over amenable edge groups or otherwise.

2. **The product-of-trees input points the wrong way.**  The locally convex
   inclusion of the Radu square complex gives
   `pi_1(S_R) -> K`.  It does not embed `K` into the BMW lattice.  Soficity
   passes to subgroups, not from a subgroup to an overgroup.

3. **No reverse embedding into a product-of-trees group.**  A group acting
   properly on a product of trees has the Haagerup property.  Subgroups
   inherit it.  Property `(T)` plus Haagerup forces a discrete group to be
   finite, so the infinite group `K` cannot be such a subgroup.  In
   particular the construction cannot be reversed into an embedding in a
   known product-of-trees model.

4. **No arithmetic/linear overgroup.**  A finitely generated linear group is
   residually finite.  A subgroup of a residually finite group is residually
   finite, whereas `K` has no nontrivial finite quotient.  Thus `K` cannot
   embed in a linear or arithmetic lattice whose soficity would descend.

5. **The finite extension is equivalent, not a solution.**  The quotient
   `barGamma/K` is `C2`; soficity is equivalent across this finite-index
   pair.  Passing to the more convenient involutory presentation changes the
   finite CSP but supplies no approximation theorem.

6. **Biautomaticity is insufficient.**  Section 4.2 supplies a normal-form
   algorithm, and the building gives a biautomatic structure.  No theorem
   makes all biautomatic or all CAT(0) groups sofic.  The free cocompact
   action on an exotic locally finite Euclidean building therefore does not
   itself construct the finite permutation models in the gate above.

7. **Perfect local models are explicitly impossible.**  Proposition
   `no_local_model` of the same paper proves that this Cayley graph has no
   perfect finite `r`-local model for any `r>=5`.  Radius-four ball rigidity
   canonically recovers the generator labels; compatibility across a
   radius-five ball then turns a perfect local model into a genuine finite
   action, and the finite residual forces that action through `C2`.  Hence an
   exact graph-cover, finite-building-quotient, or perfect random-lift route
   cannot work.  Soficity permits `o(d_n)` defective vertices, so this result
   does not decide the gate; it identifies sparse branching or defects as a
   mandatory feature of any positive model.

The gate is consequently both explicit and genuinely terminal: proving it
would answer Alekseev--Thom Open Problem 6.1 for a finitely presented sofic
Kazhdan non-residually-finite group and would close the requested exact-MF-
radical-over-`Z` theorem by taking `K x Z`.
