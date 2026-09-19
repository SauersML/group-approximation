# Ascending-HNN coset actions: the iterated-coset criterion, profinite closure, and monomial solutions

**Date:** 2026-08-18  
**Status:** proof artifact for Cairn review; not yet Lean-formalized.  
**Question:** Francesco Fournier-Facio asked whether, for an ascending HNN extension
\[
V=\langle \Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma)\rangle
\]
of a sofic or residually finite group along a proper injective self-embedding,
the coset action `V ↷ V/Γ` is sofic in the sense of Gao--Kunnawalkam
Elayavalli--Patchell (GKP).

This note records the part of that question that can be proved now without
assuming the still-open blanket implication “residually finite base implies
sofic HNN coset action.”  It contains four new theorem packages:

1. an exact **if and only if** reduction of the HNN action to the family of
   iterated base actions `Γ ↷ Γ/α^m(Γ)`;
2. the exact profinite closure of the base copy in a proper ascending HNN
   extension, showing that the existing “base copy separable in the HNN group”
   route is vacuous in every proper case;
3. a complete positive solution for monomial polynomial self-embeddings,
   including Caleb Eckhardt's one-compressor example;
4. the resulting sofic/non-MF monomial HNN-wreath family and the
   single-compressor-sofic / full Kun--Thom-action-nonsofic dichotomy.

The unrestricted residual-finiteness/soficity question remains open after
these reductions.

---

## 0. Duplicate and source audit

Repository search was performed before promoting these statements to Cairn.
The project already contains, and this note **does not re-claim**:

- the finite-index-image theorem
  `MarkedCompression.isSoficAction_vertical_cosets` in
  `GroupApproximation/Sofic/AscendingHNNCosetActionSofic.lean`;
- the arbitrary-image theorem over universally action-sofic (hence LERA/LERF)
  bases, `isSoficAction_vertical_cosets_of_uas`, in the same file;
- the `m=1` downward implication from ambient HNN action soficity to
  `Γ ↷ Γ/α(Γ)`, formalized in `AscendingHNNSoficDescent.lean`;
- the cyclic-extension permanence theorem used to pass from the telescope
  kernel to the vertical/HNN group, formalized in
  `SoficActionCyclicExtension.lean`;
- separability of the positive monomial stabilizers used in the positive-core
  argument, proved in `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md` and imported into
  Cairn by `positive-core-bernoulli-ce-proof`;
- the unconditional non-MF HNN-wreath obstruction from a proper property-(T)
  self-embedding and an involutive lamp, formalized in
  `AscendingHNNWreathWitness.lean` and represented in Cairn by the established
  compression-witness/collapse nodes;
- Kun--Thom's nonsofic full coordinate action, already imported as
  `coordinate-action-not-sofic`.

The new content is the **all-iterates equivalence**, the **profinite-closure
identity**, their use to solve the **full one-compressor HNN action** for the
monomial family, and the two corollary syntheses that use those results.

External status was rechecked on 2026-08-18 against primary sources:

- D. Gao, S. Kunnawalkam Elayavalli, G. Patchell,
  *Soficity for group actions on sets and applications*, arXiv:2401.04945v3,
  published in *Research in the Mathematical Sciences* 12 (2025), 48.
  The paper supplies the notion of sofic action and the generalized-wreath
  permanence theorem.  The repository already carries a source-verified import
  as `gkp-sofic-action-toolkit`.
- G. Kun, A. Thom, *Nonsofic wreath products of residually finite groups*,
  arXiv:2608.06222v1 (2026).  The repository already source-verifies the needed
  nonsofic wreath/coset-action input.
- N. Monod, S. Popa, *On co-amenability for groups and von Neumann algebras*,
  arXiv:math/0301348.  This supplies the classical amenability/co-amenability
  background but is not needed for the proofs below.

No priority claim is made beyond the repository-local statement “these named
packages were not already present in Cairn/Lean under an equivalent theorem
statement.”  They should be treated as new deductions in this project pending
external mathematical review.

---

## 1. Setup: telescope and height

Let `Γ` be a countable group and let
\[
\alpha:\Gamma\hookrightarrow\Gamma
\]
be an injective endomorphism.  Work in the standard vertical/telescope model
of the ascending HNN extension
\[
V=\langle\Gamma,t\mid t\gamma t^{-1}=\alpha(\gamma)\rangle.
\]
Put
\[
\Gamma_r=t^{-r}\Gamma t^r\qquad(r\ge 0).
\]
Since `t Γ t^{-1}=α(Γ)≤Γ`, these form an increasing chain
\[
\Gamma_0\le \Gamma_1\le\Gamma_2\le\cdots .
\]
Let
\[
N=\bigcup_{r\ge0}\Gamma_r.
\]
The height homomorphism `h:V→Z`, with `h(t)=1` and `h(Γ)=0`, has kernel `N`,
and
\[
V=N\rtimes\langle t\rangle.
\]
Let
\[
X=V/\Gamma.
\]
Height is well-defined on `X`, because the stabilizer `Γ` has height zero.

We use only standard permanence properties of the GKP notion, all already
represented in the repository: restriction to a subgroup, restriction to an
orbit/finite union of relevant orbits, local passage through an increasing
subgroup cover, and cyclic extension.

---

## 2. The exact all-iterates criterion

### Theorem A

The following are equivalent:

1. the action `V ↷ X=V/Γ` is sofic;
2. the action `N ↷ X` is sofic;
3. for every integer `m≥1`, the transitive base action
   \[
   \Gamma\curvearrowright \Gamma/\alpha^m(\Gamma)
   \]
   is sofic.

Thus the ascending-HNN construction itself introduces no additional soficity
obstruction beyond the full tower of iterated self-image coset actions.

### 2.1 Necessity: the HNN action contains every iterated base action

Assume `V ↷ X` is sofic.  Restrict the acting group to `Γ`; the resulting
`Γ`-action on `X` is sofic.

Fix `m≥1` and consider
\[
x_m=t^m\Gamma\in X.
\]
For `γ∈Γ`,
\[
\gamma x_m=x_m
\iff t^{-m}\gamma t^m\in\Gamma.
\]
For an ascending HNN extension,
\[
t^{-m}\gamma t^m\in\Gamma
\iff \gamma\in t^m\Gamma t^{-m}
=\alpha^m(\Gamma).
\]
Therefore
\[
\operatorname{Stab}_\Gamma(x_m)=\alpha^m(\Gamma),
\]
and the orbit map gives an equivariant bijection
\[
\Gamma/\alpha^m(\Gamma)\cong \Gamma x_m\subset X.
\]
Soficity passes to an orbit, hence every iterated action is sofic.

The same argument starting only from `N ↷ X` proves `(2)⇒(3)`, since
`Γ≤N`.

### 2.2 Sufficiency: every finite N-window is an iterated base window

Assume now that every action
\[
\Gamma\curvearrowright\Gamma/\alpha^m(\Gamma),\qquad m\ge1,
\]
is sofic.  We prove `N ↷ X` sofic directly from the finitary definition.

Take finite test sets
\[
F\subset N,\qquad E\subset X,
\]
and a tolerance `ε>0`.

For each `x∈E`, choose a representation
\[
x=n_x t^{k_x}\Gamma,
\qquad n_x\in N,\ k_x\in\mathbb Z.
\]
Because `F` and the finitely many `n_x` lie in the increasing union of the
levels, choose `R` so large that
\[
F\subset\Gamma_R,\qquad n_x\in\Gamma_R\quad(x\in E),
\]
and also
\[
R+k_x\ge0\quad(x\in E).
\]
Conjugation by `t^R` identifies `Γ_R` with `Γ`:
\[
\theta_R:\Gamma_R\stackrel\cong\longrightarrow\Gamma,
\qquad \theta_R(g)=t^Rgt^{-R}.
\]
Write
\[
a_x=\theta_R(n_x)\in\Gamma,
\qquad m_x=R+k_x\ge0.
\]
For `g=t^{-R}\gamma t^R∈Γ_R`, the stabilizer condition at `x` is
\[
g x=x
\iff t^{-k_x}n_x^{-1}g n_x t^{k_x}\in\Gamma.
\]
Substituting the displayed forms gives
\[
t^{-m_x}a_x^{-1}\gamma a_x t^{m_x}\in\Gamma,
\]
which is equivalent to
\[
a_x^{-1}\gamma a_x\in\alpha^{m_x}(\Gamma).
\]
Hence under `θ_R`,
\[
\operatorname{Stab}_{\Gamma_R}(x)
\cong a_x\alpha^{m_x}(\Gamma)a_x^{-1}.
\]
Therefore the `Γ_R`-orbit of every point of `E` is equivariantly isomorphic to
`Γ/α^{m_x}(Γ)` (for `m_x=0` the orbit is a point).  Each such orbit action is
sofic by hypothesis.  Only finitely many orbits meet `E`, so the finite union
of those orbit actions admits one common finite model on the prescribed
window.

Because `F⊂Γ_R`, that finite model already satisfies every multiplicativity,
separation and orbit-chart condition required for the `N` test window.  Extend
the approximating map from `Γ_R` to all of `N` arbitrarily; the extension is
never queried outside `Γ_R` on this test.  Thus the `N`-action is sofic.

This argument is the local version of the repository's subgroup-cover
principle: every finite `N`-window can be swallowed by one telescope level,
and the relevant pieces of that level action are iterated base coset actions.

### 2.3 The stable-letter direction adds no obstruction

The repository's already-formalized cyclic-extension theorem
`isSoficAction_semidirect` says that if the normal telescope kernel `N` acts
soficly on `X`, then adjoining the shift `t` gives a sofic action of
`N⋊Z=V`.  Therefore `(2)⇒(1)`.

Together with the restrictions above this proves Theorem A.

### 2.4 Why the criterion is stronger than the existing m=1 descent

`AscendingHNNSoficDescent.lean` proves the necessary `m=1` implication.
Theorem A shows that:

- **all** iterates are necessary, not just the first image;
- they are collectively **sufficient**;
- the remaining broad question is exactly whether the self-image actions
  `Γ ↷ Γ/α^m(Γ)` are sofic under the desired hypotheses on `Γ`.

This is the correct reduction target for the general residual-finite/sofic
problem.

---

## 3. Profinite closure of the base copy

The existing repository contains a true conditional theorem: if the base copy
`Γ≤V` is separable in `V`, then `V↷V/Γ` is sofic.  The surrounding commentary
had treated this as a potentially sharp route for a proper self-embedding.  In
fact the hypothesis never occurs in the proper case.

### Theorem B

The profinite closure of the base copy is exactly the telescope kernel:
\[
\overline{\Gamma}^{\,\mathrm{prof},V}
=N=\bigcup_{r\ge0}t^{-r}\Gamma t^r.
\]
Consequently `Γ` is separable in `V` if and only if `α` is surjective.  In
particular, for every **proper** injective self-embedding the base copy is not
separable in the HNN group.

### Proof: every finite quotient collapses the telescope levels

Let `L≤V` be finite index with `Γ≤L`.  Take the finite-index normal core
\[
C=\bigcap_{v\in V}vLv^{-1}\triangleleft V,
\]
and let
\[
q:V\to F=V/C
\]
be the finite quotient.  Set `S=q(Γ)`.

The HNN relation gives
\[
q(t)S q(t)^{-1}=q(\alpha(\Gamma))\subseteq S.
\]
Both sides are finite subgroups of the same cardinality, because conjugation
by `q(t)` is a bijection.  Hence
\[
q(t)S q(t)^{-1}=S.
\]
Therefore, for every `r≥0`,
\[
q(t^{-r}\Gamma t^r)=S.
\]
If `x∈Γ_r=t^{-r}Γt^r`, then `q(x)∈S⊂q(L)`.  Since `C≤L`,
\[
q^{-1}(q(L))=L,
\]
so `x∈L`.  Thus **every** finite-index subgroup of `V` containing `Γ`
contains every level `Γ_r`, hence contains `N`.  Therefore
\[
N\subseteq\overline{\Gamma}^{\,\mathrm{prof},V}.
\]

Conversely, if `x∉N`, then the height `h(x)` is nonzero.  Choose an integer
`d≥2` not dividing `h(x)`.  The subgroup
\[
h^{-1}(d\mathbb Z)
\]
has finite index in `V`, contains `Γ`, and excludes `x`.  Hence
\[
\overline{\Gamma}^{\,\mathrm{prof},V}\subseteq N.
\]
This proves equality.

If `α` is proper, choose `γ∈Γ\setminus α(Γ)`.  Then
\[
t^{-1}\gamma t\in t^{-1}\Gamma t\setminus\Gamma
\]
but it lies in the profinite closure of `Γ`, so the base is not separable.
If `α` is surjective, the HNN extension is a semidirect product by an
automorphism and `N=Γ`, so the base is separable via the height quotients.

### Consequence: exact finite quotients can never model the strict compression

In every finite quotient `q` of `V`,
\[
q(\Gamma)=q(\alpha(\Gamma))=q(t^{-r}\Gamma t^r)
\]
for all `r`.  Thus any proof of soficity for the proper coset action must use
genuinely approximate permutation models (or finite models of the **base
coset actions**), not literal finite quotients of `V` separating the base
stabilizer.

This does not invalidate the Lean implication
`isSoficAction_vertical_cosets_of_separable_base`; it shows that its premise is
vacuous whenever `α` is proper.  The useful separability questions live
instead at the base level, for the subgroups `α^m(Γ)≤Γ` appearing in Theorem A.

---

## 4. A sufficient criterion in the base group

Theorem A immediately yields:

### Corollary C

If each subgroup `α^m(Γ)` is separable in `Γ`, then
\[
V\curvearrowright V/\Gamma
\]
is sofic.

Indeed, a separable subgroup `H≤Γ` gives exact finite Schreier approximations
of `Γ↷Γ/H`: for a finite window in `Γ/H`, intersect finitely many finite-index
overgroups of `H` so that the quotient map is injective on that window, take a
normal core, and use the resulting finite coset action.  Apply this to
`H=α^m(Γ)` for every `m`, then use Theorem A.

The point is that this criterion is not the impossible condition “the base
copy is separable in `V`.”  It asks for subgroup separability **inside the
base**, one iterate at a time.

---

## 5. Monomial polynomial self-embeddings

The base-level criterion completely resolves Francesco's question for the
one-compressor polynomial examples that motivated it.

Let `k=F_q` be a finite field,
\[
R=k[x_1,\ldots,x_d],\qquad r\ge3,
\qquad \Gamma=\operatorname{EL}_r(R).
\]
Let
\[
A\in M_d(\mathbb N),\qquad \det A\ne0,
\]
and define a monomial ring embedding
\[
\sigma_A(x^v)=x^{Av},\qquad v\in\mathbb N^d.
\]
Because `A` is injective on `Z^d`, distinct monomials remain distinct, so
`σ_A` is injective.  Let `α_A` be the induced endomorphism of `Γ`.

For `m≥1`, put
\[
R_m=\sigma_A^m(R)=k[A^m\mathbb N^d].
\]
The monoid `A^m N^d` is freely generated by the columns of `A^m`, so `R_m` is
again a polynomial ring over `k`.  The image subgroup is
\[
\alpha_A^m(\Gamma)=\operatorname{EL}_r(R_m).
\]
By the standard Suslin stability theorem over polynomial rings over a field,
\[
\operatorname{EL}_r(R_m)=\operatorname{SL}_r(R_m)
\qquad(r\ge3).
\]
This is the same input already used in the repository's positive-core proof.

### Proposition D: every monomial self-image is separable

For every `m≥1`, `α_A^m(Γ)` is separable in `Γ`.

Take
\[
g\in\Gamma\setminus\alpha_A^m(\Gamma).
\]
If every matrix entry of `g` lay in `R_m`, then, since `det(g)=1`, we would have
\[
g\in\operatorname{SL}_r(R_m)=\operatorname{EL}_r(R_m),
\]
a contradiction.  Hence some entry `f` of `g` lies outside `R_m`.

As a `k`-vector space,
\[
R_m=\operatorname{span}_k\{x^u:u\in A^m\mathbb N^d\}.
\]
Choose an exponent `u` in the support of `f` with
\[
u\notin A^m\mathbb N^d.
\]
Choose `M` larger than every coordinate of every exponent occurring in `f`,
and form the finite monomial quotient
\[
Q_M=R/(x_1^M,\ldots,x_d^M).
\]
The surviving monomials `x^v` with `0≤v_i<M` are a `k`-basis of `Q_M`.
The image of `R_m` is spanned by those surviving basis monomials whose
exponents lie in `A^m N^d`.  Our chosen monomial `x^u` survives and is not one
of them, so
\[
\bar f\notin\overline{R_m}\subset Q_M.
\]
Reduction of matrix entries gives a finite quotient
\[
\rho_M:\Gamma\longrightarrow\operatorname{SL}_r(Q_M).
\]
Every element of `ρ_M(α_A^m(Γ))` has all entries in `\overline{R_m}`, whereas
the selected entry of `ρ_M(g)` does not.  Therefore
\[
\rho_M(g)\notin\rho_M(\alpha_A^m(\Gamma)).
\]
The preimage
\[
\rho_M^{-1}(\rho_M(\alpha_A^m(\Gamma)))
\]
is finite index in `Γ`, contains `α_A^m(Γ)`, and excludes `g`.  This proves
separability.

### Theorem E: the monomial ascending-HNN coset action is sofic

Let `V_A` be the ascending HNN extension of `Γ` along `α_A`.  Proposition D
and Corollary C give
\[
\boxed{V_A\curvearrowright V_A/\Gamma\text{ is sofic}.}
\]
There is no finite-index-image hypothesis.  In particular this handles
infinite-index monomial compressors.

### Caleb's one-compressor example

For
\[
R=\mathbb F_2[x,y],\qquad
\sigma(x)=x,\qquad \sigma(y)=xy,
\]
one has
\[
\sigma^m(R)=\mathbb F_2[x,x^m y].
\]
Thus every
\[
\operatorname{EL}_3(\mathbb F_2[x,x^m y])
\]
is separable in `EL_3(F_2[x,y])`, and the full one-compressor ascending-HNN
coset action in Caleb's construction is sofic.  This is the concrete
affirmative answer to the case Francesco was asking about in the email thread.

### Relation to the existing positive-core proof

The degree-truncation separability argument is already present in the project
for positive stabilizers.  What is new here is not that local congruence trick;
it is:

- applying it **to every iterate** of one self-embedding;
- feeding those iterates through Theorem A to obtain soficity of the **full
  ascending-HNN coset action**;
- allowing any injective nonnegative monomial matrix `A` with nonzero
  determinant, rather than only the positive unimodular compressor semigroup
  used in the Kun--Thom positive core.

---

## 6. Sofic and non-MF monomial HNN wreath products

Assume now that the monomial self-embedding is proper.  The polynomial
elementary group `Γ=EL_r(k[x_1,…,x_d])` is a finitely generated property-(T)
group for `r≥3` by the Ershov--Jaikin-Zapirain theorem used throughout the
project.  It is residually finite by congruence quotients, hence sofic.

The telescope kernel `N` is an increasing union of copies of `Γ`, so it is
sofic; `V_A/N≅Z` is amenable, hence the HNN group `V_A` is sofic.  By Theorem E
the action `V_A↷V_A/Γ` is sofic.  The lamp group `C_2` is finite/sofic, so the
GKP generalized-wreath theorem yields
\[
W_A=\left(\bigoplus_{V_A/\Gamma}C_2\right)\rtimes V_A
\]
sofic.

On the other hand, the repository's already-formalized ascending-HNN
compression-collapse theorem says that a proper injective self-embedding of a
property-(T) base with a nontrivial involutive one-site lamp produces a
nontrivial MF-radical element.  Thus the same `W_A` is not MF.

Hence every proper injective monomial self-embedding above produces
\[
\boxed{W_A\text{ sofic and non-MF}.}
\]
This includes infinite-index compressors, beyond the finite-index sofic
assembly already present in the repository.

---

## 7. Single Kun--Thom compressors versus the full multi-compressor action

Kun--Thom's polynomial/Laurent-polynomial pair contains positive elementary
monomial compressor directions such as
\[
A_{ij}=I+E_{ij}.
\]
For a fixed compressor, let
\[
V_{ij}=\langle\Gamma,t_{ij}\rangle
\]
be the corresponding one-generator ascending-HNN subgroup.  Theorem E applies
to `A_{ij}`, so
\[
V_{ij}\curvearrowright V_{ij}/\Gamma
\]
is sofic for **each individual positive compressor direction**.

By contrast, the established Cairn claim `coordinate-action-not-sofic`
imports Kun--Thom's theorem that for their full ambient group `G` the action
\[
G\curvearrowright G/\Gamma
\]
is nonsofic.  Thus:
\[
\boxed{\text{every single positive compression direction is sofic, while the
full multi-compressor action is nonsofic}.}
\]
The obstruction in the Kun--Thom pair is therefore genuinely a compatibility
phenomenon among multiple compressor directions; it is not already present in
an individual ascending-HNN direction.

This statement is distinct from the repository's separate counterexample to
GKP Question 4.2 about combining commuting actions: here the individual
actions are the one-compressor **subgroup restrictions of the same
Kun--Thom coset action**, and the conclusion identifies where the nonsoficity
first appears in that compressor geometry.

---

## 8. Exact remaining open problem

Theorem A sharpens Francesco's broad question to:

> For an injective endomorphism `α` of a residually finite (or merely sofic)
> group `Γ`, must every action
> \[
> \Gamma\curvearrowright\Gamma/\alpha^m(\Gamma)
> \]
> be sofic?

A positive answer for all `m` is **equivalent** to soficity of the ascending-HNN
coset action.  There is no additional HNN/cyclic obstruction.

Residual finiteness alone does not imply subgroup separability, so the monomial
proof cannot be promoted abstractly by replacing its congruence-separability
argument with residual finiteness.  Conversely, non-separability of some
`α^m(Γ)` does not by itself prove the corresponding action nonsofic: GKP
soficity is weaker than existence of exact finite Schreier quotients.  This is
the precise residue that remains open.

---

## 9. Formalization boundary

The following ingredients are already kernel-checked in Lean:

- telescope/vertical structure and common-level finite windows;
- finite-index and UAS positive cases;
- cyclic extension of a sofic action;
- `m=1` ambient-to-base descent;
- the HNN one-site lamp compression witness and non-MF involutive collapse.

The new theorem packages in this note are **not** claimed Lean-formalized:

1. all-iterates iff criterion;
2. profinite closure `cl_V(Γ)=N`;
3. monomial all-iterate separability assembled into full HNN-action soficity;
4. the sofic/non-MF monomial family and single-vs-multi compressor synthesis.

These are the natural next formalization targets after mathematical review.
