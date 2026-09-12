# Simultaneous permutation and operator-norm stability beyond approximability

Date: 2026-08-13

## Status

This does not introduce a fourth intrinsic approximation class on the level
of MF, sofic, or hyperlinear groups.  The ``mixed'' class used below is
literally the union

\[
\{\text{sofic groups}\}\cup\{\text{operator-MF groups}\}.
\]

It is a bookkeeping device that lets one application of the
Fournier--Facio machine control both target families at once.  The new
phenomenon is the simultaneous separation: a single group can be pointwise
stable for both metrics while belonging to neither approximation class.

The abstract argument and its concrete mixed seed are now formalized in Lean:

- `GroupApproximation/Stability/MixedApproximation.lean` defines the mixed
  class, both pointwise stability notions, the no-nontrivial-mixed-quotient
  predicate, and the Hamming-ultraproduct and norm-corona arguments.
- `GroupApproximation/Endpoint/SimultaneousStability.lean` combines the
  repository's explicit nonsofic and non-operator-MF witnesses into a closed
  mixed-family obstruction.

There is no conditional Lean existence theorem.  The final group is not
declared until the repository contains unconditional proofs of the required
Leavitt/Clifford word-problem algorithms and the Fournier-Facio
relatively-hyperbolic construction.  In particular, those gaps are not hidden
behind axioms, typeclasses, structures, or theorem-shaped hypotheses.

The new deduction is the combination

```text
effective nonsofic Q + effective non-MF W
        -> A = Q x W is non-approximable for one mixed family
        -> Fournier-Facio Proposition B
        -> simultaneous pointwise P-stability and operator-norm stability
        -> Fournier-Facio Proposition C
        -> universal H^2 nonvanishing as well.
```

No characteristic-`p` Kaplansky consequence is claimed. The proper-isometry
identity in the Leavitt algebra is algebraic, but the Kazhdan projection used
by the analytic argument is an operator-norm limit. It is not thereby an
element of a modular group ring. That route does not currently produce a
direct-finiteness counterexample.

## The mathematical target

Use the following two proved repository endpoints.

1. The group

   \[
   Q=\operatorname{EL}_4\bigl(L_{\mathbf F_2}(1,2)\bigr)
   \]

   is nonsofic.

2. The affine--Clifford construction supplies a finitely generated
   operator-norm non-MF group `W` described below.

Then there is a finitely presented infinite group \(\Lambda\) such that

\[
\begin{aligned}
&\Lambda\text{ has property }(T),\\
&\Lambda\text{ is pointwise permutation-stable},\\
&\Lambda\text{ is pointwise operator-norm matricially stable},\\
&\Lambda\text{ is nonsofic and non-MF},\\
&\Lambda\text{ has no nontrivial sofic quotient},\\
&\Lambda\text{ has no nontrivial MF quotient},\\
&\Lambda\text{ has no nontrivial finite quotient},\\
&\Lambda\text{ is not residually finite}.
\end{aligned}
\]

Moreover, \(\Lambda\) can be chosen so that

\[
H^2(\Lambda;V)\ne 0
\]

for every nonzero unitary \(\Lambda\)-representation \(V\). The word
"nonzero" makes explicit the usual convention in the cited statement: the
zero coefficient module has zero cohomology.

Here both stability assertions are pointwise. Thus an asymptotic
homomorphism is required to approach genuine homomorphisms on each fixed
group element; no uniform stability modulus is asserted.

## 1. Effective input on the nonsofic side

The repository theorem

```text
GroupApproximation.universalLeavittEL4_not_isSofic
```

gives the first input. In addition, \(Q\) has solvable word problem.

Choose the finite elementary generating set obtained from the four Leavitt
generators. A word in these group generators can be evaluated as a
\(4\times4\) matrix over \(L_{\mathbf F_2}(1,2)\). Addition,
multiplication, and equality of entries are effective because the Leavitt
algebra admits a Diamond-Lemma normal form and an explicit basis. Therefore
equality of the evaluated matrix with \(I_4\) is decidable.

This effectiveness claim is ordinary mathematics, not currently a closed Lean
endpoint. The repository file `Leavitt/LeavittNormalForm.lean` proves the
monomial spanning statement used by the algebraic development, but it does
not package a word-problem algorithm or a decidable basis normalizer.

Consequently, subject to the repository's nonsofic endpoint,

\[
\boxed{Q\text{ is a finitely generated nonsofic group with solvable word
problem}.}
\]

This also supplies a direct positive instance for the solvable-word-problem
question in Fournier-Facio's Remark 2.5: a nonsofic group with solvable word
problem exists.

## 2. Effective input on the non-MF side

Use the concrete affine base

\[
\Gamma=\mathbf Z^3\rtimes \operatorname{SL}_3(\mathbf Z),
\qquad
\beta(v,A)=(2v,A).
\]

Its mapping telescope is

\[
\Gamma_\infty\cong
\mathbf Z[1/2]^3\rtimes\operatorname{SL}_3(\mathbf Z),
\]

and the vertical group is

\[
V\cong\Gamma_\infty\rtimes_\beta\mathbf Z.
\]

Thus an element of \(V\) has effective coordinates

\[
(q,A,k),\qquad
q\in\mathbf Z[1/2]^3,
\quad A\in\operatorname{SL}_3(\mathbf Z),
\quad k\in\mathbf Z.
\]

Multiplication, inversion, and equality are exact dyadic-rational and
integer-matrix computations. Membership in the level-zero base is decidable:

\[
(q,A,k)\in\Gamma
\quad\Longleftrightarrow\quad
k=0\text{ and }q\in\mathbf Z^3.
\]

It follows that equality in the coset space

\[
X=V/\Gamma
\]

is decidable, since

\[
g\Gamma=h\Gamma
\quad\Longleftrightarrow\quad
h^{-1}g\in\Gamma.
\]

Let \(C(X)\) be the Clifford lamp group

\[
C(X)=\langle z,c_x\ (x\in X)\mid
z^2=c_x^2=1,\ z\text{ central},\
[c_x,c_y]=z\ (x\ne y)\rangle.
\]

A finite lamp word can be reduced algorithmically to

\[
z^\varepsilon c_{x_1}\cdots c_{x_r},
\]

where the sites are distinct. To remove a repeated site, commute its second
occurrence next to its first occurrence, toggle the central sign once for
each crossing, and cancel the two equal involutions. Only finitely many site
equality tests are needed.

The uniqueness check is expressed by the signed finite-support model

\[
\mathbf F_2\times\mathbf F_2^{(X)}.
\]

This carrier is equipped with the twisted Clifford multiplication

\[
(\varepsilon,f)(\delta,g)
=
(\varepsilon+\delta+B(f,g),f+g),
\]

where \(B\) counts ordered lamp crossings modulo two. It must not be
described as the ordinary direct-product group: a homomorphism from the
nonabelian Clifford group to an abelian direct product could not retain the
commutator sign. The repository's `Sofic/CliffordLampGroup.lean` implements
exactly this twisted model.

Now put

\[
W=C(X)\rtimes V.
\]

A word in \(W\) collects effectively to \((\ell,v)\). Decide \(v=1\) in
the dyadic model and then decide \(\ell=1\) by the finite-support Clifford
reduction. Hence

\[
\boxed{\operatorname{WP}(W)\text{ is decidable}.}
\]

The action of \(V\) on \(X\) is transitive, so the root lamp and a finite
generating set for \(V\) generate \(W\); the central sign is obtained from
the commutator of two distinct lamp sites. Thus \(W\) is finitely generated.

The bare extension

\[
1\longrightarrow C(X)\longrightarrow W\longrightarrow V\longrightarrow1
\]

does **not** by itself prove soficity: it has an amenable kernel and a sofic
quotient, which is the wrong direction for the general amenable-extension
theorem.  The specific finite-coset tower repairs this.

Put \(X_n=\Gamma/\beta^n(\Gamma)\) and
\(X_+=\coprod_{n\ge1}X_n\).  Each \(X_n\) has \(8^n\) elements, and

\[
g\beta^n(\Gamma)\longmapsto
\beta(g)\beta^{n+1}(\Gamma)
\]

is an injective, \(\beta\)-equivariant map \(X_n\to X_{n+1}\).  If
\(Y_m=X_1\amalg\cdots\amalg X_m\), then

\[
K_m=C(Y_m)\rtimes\Gamma
\]

is a finite extension of the residually finite group \(\Gamma\), hence is
sofic.  The increasing union \(K=C(X_+)\rtimes\Gamma\) is sofic.  Extend
the displayed injection and \(\beta\) to an injective endomorphism of
\(K\); its automorphic direct limit \(\widetilde K\) is a directed union of
copies of \(K\), hence is sofic.  Finally

\[
S=\widetilde K\rtimes\mathbb Z
\]

is sofic by the valid sofic-kernel/amenable-quotient extension theorem.
The dilated site set is \(V\)-equivariantly isomorphic to \(V/\Gamma\):
the telescope height gives transitivity and shows that the stabilizer of the
level-zero root is exactly \(\Gamma\).  Consequently

\[
S\cong C(V/\Gamma)\rtimes V=W,
\qquad
\boxed{W\text{ is sofic}.}
\]

The repository's general marked-compression argument, together with the
standard property-`(T)` theorem for
\(\mathbf Z^3\rtimes\operatorname{SL}_3(\mathbf Z)\), applies directly
inside \(W\): the Clifford sign is nontrivial, but every homomorphism from
\(W\) to an operator-norm matrix corona kills it. Therefore

\[
\boxed{W\text{ is non-MF}.}
\]

The soficity of \(W\) is a useful contrast but is not needed in the
mixed-family argument.

## 3. The mixed-family lemma

Define one family of bi-invariant metric groups by

\[
\mathcal G=
\{(\operatorname{Sym}(n),d_H):n\ge1\}
\ \cup\
\{(U(n),d_{\mathrm{op}}):n\ge1\},
\]

where \(d_{\mathrm{op}}(u,v)=\lVert u-v\rVert_{\mathrm{op}}\).

Set

\[
A=Q\times W.
\]

Then:

- \(A\) is nonsofic because it contains \(Q\), and soficity passes to
  subgroups;
- \(A\) is non-MF because it contains \(W\), and operator-norm MF passes to
  subgroups;
- \(A\) has solvable word problem by the two algorithms above.

The central observation is

\[
\boxed{A\text{ is not }\mathcal G\text{-approximable}.}
\tag{1}
\]

Indeed, suppose \(\phi_j:A\to G_j\), with \(G_j\in\mathcal G\), were an
asymptotically multiplicative and point-separating sequence. At least one of
the sets

\[
I_S=\{j:G_j\text{ is symmetric}\},
\qquad
I_U=\{j:G_j\text{ is unitary}\}
\]

is infinite. Restriction to an infinite subsequence preserves both the
vanishing multiplicative defects and the positive `liminf` separation of
every fixed nonidentity element. An infinite symmetric subsequence would
make \(A\) sofic; an infinite unitary subsequence would make \(A\) MF. Both
conclusions contradict the preceding paragraph, proving (1).

This argument uses a single mixed target family. Applying the two target
families separately would produce two unrelated output groups and would not
give simultaneous stability.

## 4. Proposition B and simultaneous stability

Apply Fournier-Facio's Proposition B to the non-\(\mathcal G\)-approximable
group \(A\) and choose \(C=\mathbf Z\). The word problem of \(A\) is
solvable and \(\mathbf Z\) is recursively presented. The proposition gives
a finitely presented group \(\Gamma_0\), hyperbolic relative to a subgroup
\(K\) containing \(\mathbf Z\), such that

\[
\Gamma_0\text{ has property }(T)
\]

and

\[
\boxed{\Gamma_0\text{ has no nontrivial }
\mathcal G\text{-approximable quotient}.}
\tag{2}
\]

The embedded copy of \(\mathbf Z\) makes \(\Gamma_0\) infinite.

For an arbitrary family of bi-invariant metric groups, every asymptotic
homomorphism is close to one factoring through an approximable quotient.
By (2), the only such quotient of \(\Gamma_0\) is the trivial quotient.
Therefore every \(\mathcal G\)-asymptotic homomorphism of \(\Gamma_0\) is
pointwise close to the trivial homomorphism.

Restricting the allowed target sequences gives both conclusions for the
same group:

\[
\boxed{\Gamma_0\text{ is pointwise P-stable}}
\]

and

\[
\boxed{\Gamma_0\text{ is pointwise operator-norm matricially stable}.}
\]

This is stronger than the existence of nearby unspecified exact actions or
representations: every asymptotic permutation action and every
operator-norm asymptotic unitary representation is close to the trivial
one.

## 5. Nonapproximability of every nontrivial quotient

If \(\Gamma_0\) were sofic, its identity quotient would contradict (2).
The same argument applies if \(\Gamma_0\) were MF. More generally, any
sofic quotient is \(\mathcal G\)-approximable using symmetric targets, and
any MF quotient is \(\mathcal G\)-approximable using unitary targets.
Consequently

\[
\boxed{\text{every nontrivial quotient of }\Gamma_0
\text{ is both nonsofic and non-MF}.}
\tag{3}
\]

Every finite group is sofic and MF, so (3) rules out nontrivial finite
quotients. Since \(\Gamma_0\) is infinite, it is not residually finite.

## 6. Proposition C and the cohomological upgrade

Apply Fournier-Facio's Proposition C to \(\Gamma_0\). It gives a finitely
presented quotient

\[
\Gamma_0\twoheadrightarrow\Lambda
\]

such that

\[
H^2(\Lambda;V)\ne0
\]

for every nonzero unitary \(\Lambda\)-representation \(V\). The restriction
of the quotient map to the parabolic subgroup \(K\) has finite kernel. Its
intersection with the embedded torsion-free copy of \(\mathbf Z\) is
therefore trivial, so \(\Lambda\) remains infinite.

Property `(T)` passes to quotients. Property (2) also passes to quotients:
any nontrivial \(\mathcal G\)-approximable quotient of \(\Lambda\) would,
after composition, be such a quotient of \(\Gamma_0\). Thus all stability,
nonapproximability, quotient, finite-quotient, and residual-finiteness
conclusions above hold for \(\Lambda\).

The result is deliberately paradoxical in shape: operator-norm stability
coexists with nonvanishing \(H^2(\Lambda;V)\) for every nonzero unitary
coefficient module. The stability does not arise from cohomology vanishing;
it is vacuous stability forced by the absence of nontrivial approximable
quotients.

## 7. Dependency and verification ledger

| Item | Status |
| --- | --- |
| \(Q\) is nonsofic | Repository Lean endpoint |
| \(W\) is operator-norm non-MF | Repository Lean theorem `ChosenNonMFTheorem.countableWitness_not_isOperatorMF` |
| \(W\) is sofic | Unconditional finite-coset-tower proof: finite Clifford stages, directed automorphic dilation, then a sofic-kernel/amenable-quotient extension; not needed for the theorem |
| Word problem of \(Q\) | Derived from an effective Leavitt normal form; not packaged in Lean |
| Word problem of \(W\) | Derived from dyadic vertical coordinates and the twisted finite-support lamp model; not packaged in Lean |
| Mixed-family nonapproximability of \(A\) | Lean theorem `simultaneousStabilitySeed_not_isMixedApproximable` |
| Construction of \(\Gamma_0\) | External Proposition B; no Lean declaration until formalized unconditionally |
| Pointwise stability from absence of approximable quotients | Proved in Lean via a bad-set Hamming ultraproduct and the cofinite norm corona |
| Construction and cohomology of \(\Lambda\) | External Proposition C; no Lean declaration until formalized unconditionally |
| Full displayed profile | Mathematical target only; not currently a Lean theorem |
| Priority or novelty of the combined theorem | Not established by this note; requires a separate literature audit |

No claim in this note should be moved into the verified README headline or a
manuscript theorem without making these dependency boundaries explicit.

## References

1. R. Hazrat and R. Preusser, [*Applications of normal forms for weighted
   Leavitt path algebras: simple rings and
   domains*](https://arxiv.org/abs/1607.05499), arXiv:1607.05499.
2. F. Fournier-Facio, [*Stability, approximable quotients, and higher
   property (T)*](https://arxiv.org/html/2512.09180v2),
   arXiv:2512.09180v2, especially Proposition B, Proposition C, and Remark
   2.5. The HTML manuscript is dated August 11, 2026; arXiv's submission
   history records v2 as uploaded June 8, 2026.
3. T. Shulman, [*The MF property for amalgamated free
   products*](https://arxiv.org/abs/2603.13564), arXiv:2603.13564, for the
   operator-norm approximate-unitary formulation of group MF.
