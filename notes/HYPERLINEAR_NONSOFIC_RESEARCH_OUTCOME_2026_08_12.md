# Hyperlinear versus sofic: research outcome and exact remaining gates

Date: 2026-08-12

## Status

This investigation does **not** produce a valid proof that Thom's group
`K` is nonsofic, nor a proof that any hyperlinear nonsofic group exists.
It pushes both the `K`-specific centralizer strategy and several broader
constructions far enough to isolate the remaining obstruction in multiple
equivalent forms. None of the available theorems removes that obstruction;
inserting the missing step would amount to assuming a major new stability or
trace-selection theorem.

The strongest rigorous conclusions are:

1. the Prüfer tower in `K` forces increasingly strong finite-level
   divisibility, but not a dominant centralizer orbit;
2. functorial product and balanced amplifications cannot universally turn a
   sofic approximation into one with transitive centralizer while preserving
   Hamming control;
3. a weak-MF nonsofic group with a nontrivial finite-order central element in
   its full sofic radical would yield a hyperlinear nonsofic image by a
   rank-insensitive spectral-corner argument;
4. the canonical Clifford cover does not satisfy that weak-MF premise;
5. the established weak-MF nonsofic symmetric double is still blocked by
   trace selection: operator-norm visibility in a Kazhdan corner does not
   imply positive normalized matrix rank.

No claim below should be read as a proof of `K` nonsoficity or of the
existence of a hyperlinear nonsofic group.

## I. The Alekseev--Thom route for `K`

Let

\[
1\longrightarrow C_{p^\infty}
\longrightarrow K
\longrightarrow Q
\longrightarrow 1
\]

denote the central extension supplied by the image of

\[
\mathbb Z[1/p]/\mathbb Z\cong C_{p^\infty}
\]

in `K`. Only the inclusion `C_{p^\infty}\leq Z(K)` is needed; equality with
the full center is unnecessary.

The dilation induces

\[
\alpha:K\longrightarrow K,
\qquad
\ker(\alpha^m)=F_m\cong C_{p^m},
\qquad
K/F_m\cong K.
\]

The inverse dilation does not descend to `K`. The map `\alpha` cannot be
implemented by conjugation in any faithful representation: conjugation is
injective, whereas `\alpha` kills `F_1`.

Alekseev--Thom prove that a Kazhdan group possessing a sofic embedding with
ergodic Loeb centralizer is LEF; if the group is finitely presented, it is
then residually finite. They formulate the existence of an
ergodic-centralizer embedding as an additional hypothesis, not as a
consequence of soficity. Their paper still identifies the de
Cornulier--Thom examples as unresolved by this method.

Thus the desired proof remains exactly

\[
K\text{ sofic}
\Longrightarrow
\exists\pi:K\hookrightarrow
\prod_{\mathcal U}\operatorname{Sym}(X_n)
\quad
C(\pi(K))\curvearrowright X_{\mathcal U}
\text{ ergodically}.
\tag{1}
\]

For an Alekseev--Thom finite centralizer lift `A_n`, this is equivalent to

\[
\lim_{\mathcal U}
\max_{x\in X_n}
\frac{|A_nx|}{|X_n|}
=1.
\tag{2}
\]

### 1. What the Prüfer tower actually forces

Even granting the strongest possible finite-level realization---that
`F_m` acts exactly, freely, and centrally inside `A_n`---one obtains only

\[
p^m\mid |A_nx|.
\tag{3}
\]

There is no resulting lower bound on

\[
\frac{|A_nx|}{|X_n|}.
\]

The number of `A_n`-orbits can grow at least as fast as their common
`p`-power divisor.

Quotienting by `F_m` cannot improve the ratio, because

\[
\frac{|A_nx|/p^m}{|X_n|/p^m}
=
\frac{|A_nx|}{|X_n|}.
\tag{4}
\]

The self-quotient `K/F_m\cong K` therefore reproduces the same orbit profile
rather than concentrating it. The corresponding group-von-Neumann-algebra
corners give the same calibration: the central projections have trace
`p^{-m}`, and the normalized corners are again isomorphic to the original
algebra.

### 2. A sharper finite-centralizer divisibility lemma

There is a stronger arithmetic constraint than (3), but it still does not
prove orbit dominance.

**Lemma.** Let `c\in\operatorname{Sym}(\Omega)` consist of `b` free cycles
of length `N`. Suppose
`u,v\in C_{\operatorname{Sym}(\Omega)}(c)` and

\[
[u,v]=c.
\]

Then

\[
N\mid b.
\tag{5}
\]

**Proof.** Identify

\[
C_{\operatorname{Sym}(\Omega)}(c)
\cong C_N^b\rtimes\operatorname{Sym}(b).
\]

There is a homomorphism

\[
\Sigma:C_N^b\rtimes\operatorname{Sym}(b)\longrightarrow C_N,
\qquad
\Sigma((r_1,\ldots,r_b),\tau)=\sum_{j=1}^b r_j.
\]

Every commutator lies in `\ker\Sigma`. The element `c` is the uniform
rotation

\[
((1,\ldots,1),1),
\]

so

\[
\Sigma(c)=b\pmod N.
\]

Consequently `b=0\pmod N`. \(\square\)

For `K`, every central element `c_m` of order `p^m` is represented by a
root-group commutator. Therefore, on any finite stage where the relevant
centrality and commutator relations have been repaired exactly, not only
does `c_m` act in `p^m`-cycles, but the number of those cycles is itself
divisible by `p^m`. Hence the repaired sector has size divisible by

\[
p^{2m}.
\tag{6}
\]

Additional independent Heisenberg pairs yield higher divisibility powers.
This is genuine extra rigidity, but it is still compatible with soficity:
the model dimensions may grow arbitrarily rapidly while the level
`m=m_n` grows arbitrarily slowly. No contradiction follows from (6).

### 3. Why property `(T)` does not collapse the multiplicity base

Let

\[
\mathcal O_n=X_n/A_n
\]

be the finite set of centralizer orbits. The `K`-labels induce an approximate
action on `\mathcal O_n`. Property `(T)` can make the corresponding quotient
graphs into expanders, but an expander may have arbitrarily many vertices.

The key distinction is

\[
A_n\text{-orbits are permuted by }K;
\quad
\text{they are not individually almost }K\text{-invariant}.
\]

Ordinary Kazhdan expansion therefore gives no reason for the effective
number of `A_n`-orbits to equal one. This remains true after passing to every
finite central quotient.

### 4. Why tensor, product, and balanced amplifications do not extremalize

One tempting general construction is to replace `X_n` by a high Cartesian
power and use coordinate permutations as a large centralizer.

Unrestricted product powers retain nontrivial histogram invariants.
Restricting to one histogram class makes the coordinate-permutation
centralizer transitive, but destroys Hamming continuity: if a tuple contains
every base point and two permutations differ at even one base point, their
induced permutations differ on every balanced tuple.

More abstractly, if `\operatorname{Sym}(d)` acts transitively on
`\operatorname{Sym}(d)/H`, its centralizer is transitive exactly when `H` is
normal. For `d\geq5`, the relevant normal subgroups are essentially

\[
1,\qquad A_d,\qquad \operatorname{Sym}(d).
\]

The regular choice `H=1` changes every point whenever the underlying
permutations are unequal; the `A_d`-quotient records only the sign and kills
all even defects. Thus no functorial transitive-centralizer amplification can
simultaneously retain Hamming-small multiplication errors and separate the
group.

This gives a finite-level explanation for why a universal amplification
proof of the Hayes--Kunnawalkam Elayavalli conjecture is unavailable.

### 5. The exact remaining `K`-theorem

The `K`-specific problem has two equivalent forms.

#### Relative matching form

Let `\sigma_n` be a hypothetical sofic approximation. Quotient it by `F_m`,
identify `K/F_m\cong K`, and amplify back by `p^m`. One needs levels
`m=m_n\to\infty` and permutations `T_n` such that, for a finite generating
set `S`,

\[
\max_{s\in S}
d_{\mathrm{Hamm}}\!\left(
T_n\sigma_n(s)T_n^{-1},
\operatorname{Amp}_{p^{m_n}}
(\sigma_n/F_{m_n})(s)
\right)
\longrightarrow0.
\tag{7}
\]

The intertwiners `T_n` must also respect the `F_{m_n}`-fiber structure.

#### Cohomological form

Writing `K` as an unbounded central extension of `Q`, the `F_m`-fiber model
defines a finite-valued extension cocycle over the quotient action. One must
show that this cocycle becomes an approximate coboundary uniformly as
`m\to\infty`.

Ordinary character agreement does not provide (7): all sofic
approximations have the same limiting regular character. Ordinary property
`(T)` does not provide it either. A theorem proving (7) would be a new
relative permutation-stability theorem for this specific central extension.
No valid route from the explicit root relations to (7) is currently known.

## II. The strongest broader reduction

The Kun--Thom construction provides an explicit nonsofic group

\[
W=\left(\bigoplus_{G/\Gamma}C_2\right)\rtimes G
\]

and, more sharply, an explicit involution `w` in its full sofic radical:

\[
1\neq w\in\operatorname{Rad}_{\mathrm{sof}}(W).
\]

The repository computes the entire radical and shows that `w` normally
generates it. Thus any homomorphism

\[
\rho:W\longrightarrow U(M)
\]

into a Connes-embeddable finite algebra with `\rho(w)\neq1` produces a
hyperlinear nonsofic image.

The perfect index-two subgroup

\[
P_2=I_{G/\Gamma}\rtimes G=[W,W]
\]

is also finitely generated and nonsofic. Hyperlinearity of `P_2` is
equivalent to hyperlinearity of `W`.

### Central-radical corner theorem

**Theorem.** Suppose `E` is weak/operator-norm MF and contains a
nonidentity finite-order central element

\[
z\in Z(E)\cap\operatorname{Rad}_{\mathrm{sof}}(E).
\]

Then a hyperlinear nonsofic group exists.

**Proof.** Embed

\[
E\hookrightarrow
U\left(
\prod_n M_{d_n}(\mathbb C)/
\bigoplus_n M_{d_n}(\mathbb C)
\right).
\]

Choose a nontrivial spectral projection `e` of the image of `z`. Since `z`
is central, `e` is a nonzero central projection. Lift `e` to projections
`e_n`, compress the unitary lifts to `e_nM_{d_n}e_n`, and normalize the
corner traces.

Centrality ensures that compression preserves asymptotic multiplicativity
in operator norm, hence in normalized Hilbert--Schmidt norm. On the
compressed tracial ultraproduct, `z` acts as a fixed nontrivial root of
unity, so it survives. The resulting image is hyperlinear.

If that image were sofic, the quotient map from `E` to it would kill `z`,
because `z\in\operatorname{Rad}_{\mathrm{sof}}(E)`, a contradiction.
\(\square\)

This theorem is rank-insensitive: the selected spectral sector may have
vanishing relative rank before compression. It gives a concrete sufficient
condition for the broader goal:

\[
\boxed{
\text{Construct one weak-MF nonsofic group with a finite central radical element.}
}
\tag{8}
\]

## III. Why the available central covers do not satisfy (8)

### 1. The Clifford cover

There is a canonical central extension

\[
1\longrightarrow\langle z\rangle\cong C_2
\longrightarrow E_{\mathrm{Cl},0}
\longrightarrow P_2
\longrightarrow1
\]

with `z` represented by the Clifford sign. Its negative central character
gives the crossed product

\[
A_{\mathrm{CAR}}\rtimes G,
\]

or equivalently the full Clifford crossed product

\[
\operatorname{Cl}(G/\Gamma)\rtimes G.
\]

The root Majorana is fixed by `\Gamma` and is moved a squared `L^2`-distance
`2` by a strict predecessor. Thus Connes embeddability of this crossed
product would immediately give a hyperlinear nonsofic group.

But the corresponding group is **not** weak MF. In every homomorphism into a
norm quotient of matrices, property `(T)`, the compressor relation, and
stable finiteness force the negative `z=-1` sector to vanish. Therefore every
norm-MF representation kills `z`. The central-radical corner theorem cannot
be applied to this cover.

### 2. The shear cover

Starting with a radical element `x`, one can adjoin a central involution `z`
and a stable letter satisfying

\[
sxs^{-1}=xz.
\]

Then

\[
z=[s,x]
\]

is central and belongs to the full sofic radical.

For the available weak-MF free-lamp group, `x` has infinite order. On the
`z=-1` sector, the missing norm-MF compatibility becomes the concrete
antipodal relation

\[
\left\|
S_n\phi_n(x)S_n^*+\phi_n(x)
\right\|_{\mathrm{op}}
\longrightarrow0.
\tag{9}
\]

Producing (9) would already force

\[
\operatorname{tr}_{d_n}(\phi_n(x))\longrightarrow0
\]

and hence give a hyperlinear nonsofic image directly. Thus the shear
construction does not merely need a routine amalgamation theorem: its
compatibility condition is already the entire norm-to-trace breakthrough.

The related free-central-jet formulation reduces the same issue to one
asymptotic Weyl relation

\[
\left\|
U_n(x)T_nU_n(x)^*T_n^*
-e^{i\varepsilon_n}1
\right\|_2=o(\varepsilon_n).
\tag{10}
\]

Relation (10) itself forces the spectral distribution of `U_n(x)` to
converge to Haar measure and therefore already solves the trace-visibility
problem. It is a sharp reformulation rather than an easier construction.

## IV. The weak-MF symmetric double and its trace gap

For a residually finite `G` and arbitrary `\Gamma<G`, the symmetric double

\[
D=G*_{\Gamma}G
\]

is weak MF. The proof embeds `G` through its profinite regular completion,
uses the MF algebra `A`, its subalgebra `C`, and Shulman's theorem

\[
A*_C A\ \text{is MF}.
\]

The regular GNS quotient detects the Bass--Serre normal form and therefore
proves that the group itself embeds in the MF amalgam. Shulman's Theorem 10
states that `A*_C A` is MF whenever `A` is separable MF and `C\subseteq A`.

For the Kun--Thom pair this yields a weak-MF nonsofic double with a fixed
radical witness. The Kazhdan projection of `\Gamma` also gives a corner `q`
such that the witness is operator-norm visible entirely in `q`.

The remaining gap is

\[
q(w-1)\neq0\quad\text{in operator norm}
\]

does not imply

\[
\tau\!\left(q(w-1)^*(w-1)q\right)>0
\]

for any matrix-ultralimit trace. The nonzero part can live on a vanishing
fraction of the lifted corner ranks.

### Why Shulman's representation lifting does not close the gap

The MF amalgam has a quotient onto

\[
L(D),
\]

whose regular trace sees every nonidentity group word. One might therefore
hope that Shulman's lifting proof automatically gives microstates for that
trace. It does not.

Her MF characterization says that every representation into `B(H)` lifts to
matrices whose sequences converge in the strong-* topology. The quotient map
records the strong-* operator limit, not the normalized matrix traces.

Consequently, the summand carrying the regular representation may occupy
asymptotically zero normalized rank. A projection onto that summand belongs
to the representation's commutant, not generally to the algebra, and
Shulman's commutant-lifting lemma does not impose a positive rank ratio.

This precisely explains why

\[
\text{MF algebra}+\text{a tracial quotient}
\]

does not imply that the quotient trace is Connes embeddable.

For a general amalgam, Shulman's exact criterion requires compatible
embeddings of the two vertex algebras into one norm matrix corona.
Compatibility on the edge is not automatic.

## V. Other routes tested

### Operator-norm Ulam stability

Most higher-rank lattices, including `\operatorname{SL}_n` over rings of
`S`-integers in the known cases, are uniformly stable for finite-dimensional
unitary almost-representations in submultiplicative norms.

If the full Kun--Thom vertex group `G` satisfied the required operator-norm
stability, the weak-MF free-lamp models would collapse to exact
finite-dimensional vertex representations, and finite-dimensional
commutant rigidity would kill the radical word. The particular
semidirect-product `G` used by Kun--Thom is not covered by the existing
high-rank-lattice theorems. Establishing such stability would prove that the
free-lamp group is not weak MF; it would not produce a hyperlinear model.

The result that `\mathbb Z^2` is flexibly operator-norm stable does not give
the needed **relative** lift in which a prescribed embedding of the cyclic
edge is conjugated to its antipode.

### Gaussian and Bogoliubov crossed products

No theorem was found asserting that a Gaussian, CAR, or Bogoliubov crossed
product of an arbitrary hyperlinear group is automatically Connes
embeddable.

There is also a conceptual obstruction. The required quasi-regular
representation of `G` contains a nonzero `\Gamma`-fixed vector. If that
representation were weakly contained in the regular representation of `G`,
then the trivial representation of the nonamenable group `\Gamma` would be
weakly contained in its regular representation, forcing `\Gamma` to be
amenable. Thus every regular-approximation construction necessarily loses
the relative wall.

### Centralizer ergodic decomposition

Measure-theoretically, one can decompose the Loeb action of the centralizer
into ergodic components, and almost every such component remains free for
the countable group `K`.

The missing point is that an ergodic component need not be an internal Loeb
subset of positive measure. Restricting to it need not produce another
permutation-ultraproduct embedding. Turning measurable ergodic components
into internal finite models is essentially the Hayes--Kunnawalkam
Elayavalli conjecture itself.

### `L^2`-invariants and self-quotients

The identities `K/F_m\cong K` force any `L^2`-Betti numbers to satisfy

\[
\beta_j^{(2)}(K)=p^{-m}\beta_j^{(2)}(K),
\]

so all such invariants vanish whenever the usual scaling theorem applies.
Thus `L^2`-Betti numbers cannot obstruct the self-quotient. Corresponding
torsion arguments lack the necessary finite-classifying-space hypotheses
because of the unbounded torsion center.

## Final status: three exact research gates

### Thom `K` gate

Prove the fiber-compatible relative matching theorem (7), or equivalently
prove that the unbounded `p`-primary extension cocycle becomes uniformly
coboundary in a hypothetical sofic approximation.

That would prove (1). Alekseev--Thom would then imply residual finiteness,
contradicting the Prüfer center.

### Central-radical gate

Construct one weak-MF group with

\[
1\neq z\in Z(E)\cap\operatorname{Rad}_{\mathrm{sof}}(E)
\]

of finite order. The central-radical corner theorem would immediately give a
hyperlinear nonsofic image.

### Trace-selection gate

For the established weak-MF nonsofic symmetric double, construct one
matrix-ultralimit trace on its canonical Kazhdan corner satisfying

\[
\tau\!\left((w-1)^*(w-1)\right)>0.
\]

Equivalently, produce the antipodal profile (9), the first-order Weyl profile
(10), or Connes embeddability of the corresponding Clifford/CAR crossed
product.

None of these gates is closed. In particular, there is no sound argument
here proving `K` nonsofic or proving the broader hyperlinear-nonsofic
conclusion. The finite-centralizer divisibility lemma, amplification no-go,
and central-radical corner theorem sharpen the frontier but do not constitute
the final counterexample.

## Related repository notes

- [`FALSE_THOM_K_DOMINANT_CENTRALIZER_AUDIT.md`](FALSE_THOM_K_DOMINANT_CENTRALIZER_AUDIT.md)
  gives the detailed audit of the Prüfer-center and dominant-orbit route.
- [`PERFECT_CORE_KUN_THOM_WREATH.md`](PERFECT_CORE_KUN_THOM_WREATH.md)
  identifies the perfect index-two nonsofic core.
- [`WEAK_MF_NONSOFIC_DOUBLE.md`](WEAK_MF_NONSOFIC_DOUBLE.md) proves the
  weak-MF symmetric-double theorem and records its Kun--Thom application.
- [`FALSE_SHULMAN_TRACE_AUDIT.md`](FALSE_SHULMAN_TRACE_AUDIT.md) isolates the
  strong-* versus normalized-trace gap in Shulman's lifting results.
- [`FALSE_CLIFFORD_NORM_MF_STERILITY.md`](FALSE_CLIFFORD_NORM_MF_STERILITY.md)
  proves that the negative Clifford sector cannot survive in a norm-matrix
  model.
- [`CENTRAL_RADICAL_SHEAR_GADGET.md`](CENTRAL_RADICAL_SHEAR_GADGET.md) develops
  the central-radical shear construction and its compatibility obstruction.
- [`FALSE_RECENT_LITERATURE_AUDIT.md`](FALSE_RECENT_LITERATURE_AUDIT.md)
  records the broader literature boundary.

## References

1. Alekseev--Thom, *Centralizers of sofic approximations of Kazhdan groups*,
   [arXiv:2608.05362](https://arxiv.org/abs/2608.05362).
2. Shulman, *The MF property for amalgamated free products*,
   [arXiv:2603.13564](https://arxiv.org/abs/2603.13564).
3. *Uniform stability of higher-rank lattices in submultiplicative norms*,
   [arXiv:2301.00476](https://arxiv.org/abs/2301.00476).
4. Lubotzky--Salomon, *Z^2 is flexibly stable in the operator norm*,
   [arXiv:2607.17578](https://arxiv.org/abs/2607.17578).
