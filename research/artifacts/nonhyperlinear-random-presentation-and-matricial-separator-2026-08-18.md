# Two orthogonal programs for the explicit nonhyperlinear-group goal

**Date:** 2026-08-18  
**Status:** research program; no nonhyperlinear group is claimed here.

This note was developed against the live `main` branch after the goal flag moved to
`non-hyperlinear-group`.  It deliberately does **not** use the program's dominant
mechanisms: property-(T) compression, flexible HS-stability, commutant recovery,
scale indices, Leavitt/Pauli decoding, Cartan/masa reconstruction, Kun--Thom
rigidity, phase-safe toric/nonlocal-game compilation, or the concurrently added
Q3.4 de-Finetti/traffic/Markovization lanes.

The two programs below come instead from:

1. probabilistic combinatorial group theory + random-matrix word maps + metric
   entropy + approximate-group inverse theory;
2. noncommutative real algebraic geometry + trace-polynomial optimization +
   invariant theory of matrices.

The first program contains a deterministic reduction that can be proved now.  Its
new open theorem is an entropy/return estimate.  The second gives a very concrete
certificate language for attacking the already explicit rank-five atlas
presentation, together with a useful no-go that says which Positivstellensatz
language cannot possibly prove the needed inequality.

---

## I. Random relators as a microstate annihilator

### 1. The finite criterion to attack

Use normalized Hilbert--Schmidt distance

```text
d2(U,V)^2 = tr_n((U-V)^*(U-V)) = 2 - 2 Re tr_n(U*V).
```

Pestov's finite criterion for hyperlinearity can be normalized so that for every
finite subset there are arbitrarily accurate unitary almost-homomorphisms whose
distances on distinct tested elements are bounded below by a fixed constant
(e.g. `1/4`; in fact the constant can be pushed toward `sqrt(2)`).  Thus a
finite presentation is nonhyperlinear as soon as one finite ball of group words
has a **dimension-independent positive defect floor** among all unitary tuples
that keep that ball pairwise separated.

For a reduced word `w` of length at most `L`, evaluation is `L`-Lipschitz in the
following elementary sense: if `max_i d2(U_i,V_i) <= eta`, then

```text
d2(w(U),w(V)) <= L eta.
```

This is the telescoping identity plus bi-invariance of `d2`.  It is the only
analytic input needed for the net argument below.

### 2. A deterministic probabilistic-method criterion

Fix:

- `k` free generators;
- a short-word radius `R`;
- a relator length `L` with `R << L`;
- `m` relators sampled independently from a finite distribution `mu_L` on
  cyclically reduced length-`L` words;
- `delta > 0`, the required separation on distinct words in the free ball
  `B_R`;
- relator tolerance `eps > 0` and net radius `eta` with `L eta` much smaller
  than `eps`.

For each matrix size `n`, let

```text
K_n(R,delta)
 = { U in U(n)^k : d2(a(U),b(U)) >= delta
                     for every distinct a,b in B_R }.
```

Choose a finite `eta`-net `N_n` for `K_n(R,delta)` (or for the slightly relaxed
`delta-L_R eta` set, so that a nearby genuinely separated tuple is still
covered).  For `U in N_n`, define its one-relator return probability

```text
p_n(U) = Pr_{r~mu_L}[ d2(r(U),I) <= 2 eps ].
```

Let `SC` be the event that the sampled `m`-tuple of relators satisfies a small
cancellation condition strong enough that the free ball `B_R` injects into the
presented group; for equal long relators, classical `C'(1/6)` with `R<L/4` is
more than enough by the Greendlinger argument.

**Net-killing criterion.**  If

```text
sum_{n>=1} sum_{U in N_n} p_n(U)^m  <  Pr(SC),
```

then some sampled relator tuple is simultaneously small-cancellation and has no
`eps`-accurate separated unitary model in **any** dimension.  The resulting
finite presentation is therefore nonhyperlinear.

**Proof.**  At one net point `U`, independence of the sampled relators makes the
probability that all `m` relators land in the `2 eps` ball exactly `p_n(U)^m`.
The union bound over every net point in every dimension is the left-hand side.
Hence with probability strictly less than `Pr(SC)` there is any bad net point.
So there is an outcome in `SC` with no bad net point.  If an actual tuple `V`
had all relator defects at most `eps`, an `eta`-near net point `U` would have all
relator defects at most `eps + L eta < 2 eps`, contradiction.  Small cancellation
makes the short free ball genuinely distinct in the quotient.  A hyperlinear
model of that quotient, restricted to that finite ball and taken with
sufficiently small multiplicative error, would give exactly the forbidden
separated generator tuple by another finite telescoping estimate.  QED.

This is a useful reduction because it asks for a **summable return estimate**,
not stability of approximate representations and not a decoder into any exact
finite-dimensional representation.

### 3. The first naive estimate is false -- and the repair is the main new idea

It is tempting to ask for

```text
Pr_r[d2(r(U),I)<=eps] <= exp(-c n^2)
```

uniformly over every separated `U in U(n)^k`.  That cannot be true.

If every `U_i` is a scalar unitary, or if a fixed `d x d` tuple is repeated with
large multiplicity, the distribution of `r(U)` does not acquire any new
`n^2`-scale anti-concentration as the multiplicity grows.  Yet the same tuple
has been embedded into arbitrarily large matrices.  Thus **matrix dimension is
the wrong complexity parameter**.

The replacement is:

> Match the negative logarithm of word-return probability to the metric entropy
> of the tuple's **simultaneous-conjugacy / representation-type stratum**, not to
> `n^2` blindly.

Repeated-block tuples have low moduli entropy even though their conjugacy
orbits are huge; all points on one simultaneous conjugacy orbit have exactly
the same relator defects and separation statistics, so those orbit directions
should never be paid for in a union bound.  Scalar and low-dimensional block
strata need only low-dimensional Littlewood--Offord/Fourier anti-concentration.
Genuinely high-complexity irreducible strata are where `exp(-c n^2)` return
bounds are both plausible and necessary.

A theorem of exactly this form would make the net-killing criterion realistic.

### 4. Three mathematical engines for the entropy/return theorem

#### 4.1 Generic stratum: word-map small balls

Avni--Glazer--Larsen prove a dimension-uniform small-ball theorem for every
fixed nontrivial word on `SU(n)`: the Haar measure of a small ball under the
word measure is bounded by a positive power (depending on the word, not on
`n`) of the Haar volume of that ball.  They also prove uniform smoothing after
a word-dependent convolution power.

This is **not** yet the theorem we need: their randomness is a Haar-random
matrix tuple with a fixed word, whereas the probabilistic construction samples
a random relator at a fixed tuple.  But there is a useful bridge.  If `mu_L` is
supported on finitely many nontrivial length-`L` words and

```text
p(U)=Pr_{r~mu_L}[r(U) is eps-close to I],
```

then Fubini converts the fixed-word small-ball estimates into an average bound
on `p(U)` over Haar-random tuples.  Markov's inequality then says that the
high-return locus `{p>=t}` has small Haar measure.  With a radius gap
`eps -> eps+L eta`, packing by disjoint HS balls converts small Haar measure into
an upper bound for the number of high-return net representatives.

The remaining difficulty is precisely the structured locus where the volume
bound loses against covering entropy.  That is where the next two engines
enter.

#### 4.2 High return as additive-combinatorial structure

High return probability for a random walk is a multiplicative-energy signal.
The noncommutative Balog--Szemeredi--Gowers philosophy turns high energy into an
approximate subgroup.  Breuillard--Green prove that approximate subgroups of
`U_n(C)` are almost abelian; the Breuillard--Green--Tao structure theorem gives
the broader finite-by-nilpotent picture for approximate groups.

The proposed use is contrapositive and quantitative:

```text
word return too large
  => a bounded word ball has high multiplicative energy
  => an approximate subgroup controls the generated packet
  => after simultaneous conjugacy, the tuple lies near a low-complexity
     almost-abelian / finite-by-nilpotent stratum.
```

Then the union bound charges only the entropy of that structured stratum.
The literature theorems are not in the normalized-HS/moduli-entropy form
needed here, and their dimension dependence must be audited rather than swept
under the rug.  That quantitative conversion is a serious theorem target, not
a citation shortcut.

#### 4.3 Abelian and repeated-block strata: Fourier / Littlewood--Offord

On a commuting diagonal tuple, a random reduced word is governed by its random
exponent-sum vector evaluated on the joint eigenvalue phases.  The return event
is therefore a toral small-ball problem for an explicit lattice random walk.
The number of phase parameters is the entropy scale; it does not grow merely
because the same block is repeated many times.

This makes the scalar counterexample to the naive `exp(-c n^2)` estimate a
feature rather than a bug: its return probability is only low-dimensional, but
so is its quotient-moduli covering number.  The same analysis should extend to
finite direct sums of bounded-size blocks and provide the base cases for an
induction on representation type.

### 5. Why random small-cancellation presentations are a natural host

Two existing results point in the same direction without solving the normalized
HS problem:

- Bassino--Nicaud--Weil prove broad generic small-cancellation results for
  random finite presentations in few-relator and more general models.
- Kozma--Lubotzky prove that, for every **fixed** representation degree `d`, a
  positive-density Gromov random group asymptotically almost surely has no
  nontrivial degree-`d` linear representation over any field.

The second result is emphatically not enough for nonhyperlinearity because the
matrix dimension in a microstate may diverge and the relations are only
approximately satisfied.  Its value here is as evidence that random relators
already destroy low-dimensional representation varieties; the proposed
entropy/return theorem is the missing uniform-in-dimension, approximate version.

### 6. Concrete experiments that test the right theorem rather than the false one

For `n=2,...,10`, sample `k`-tuples and random reduced words of lengths
`L=20,40,80`.  For each tuple record:

1. empirical `p(U)=Pr[d2(r(U),I)<eps]`;
2. approximate simultaneous-commutant dimension (small singular values of the
   linear commutator map `X -> ([X,U_i])_i`);
3. block/repetition structure after numerical joint-algebra decomposition;
4. a quotient-moduli proxy obtained by removing simultaneous-conjugacy tangent
   directions from the local Gram matrix.

The falsifiable prediction is not `-log p ~ n^2`; it is that `-log p` tracks
**quotient complexity**.  If high-return tuples occur with genuinely large
quotient entropy, the program is probably dead.  If they collapse onto
commuting/repeated-block strata, the BSG/inverse-theorem route is exactly the
right next theorem.

---

## II. A matricial-only trace-polynomial separator for the explicit atlas presentation

### 7. The certificate shape

The repository now has an explicit finite rank-five atlas/Steinberg relator
list (`atlas-steinberg-rank-five-translation`).  Forget the Leavitt decoder,
Pauli carriers, PVMs and commutants entirely and regard those relators only as a
finite polynomial constraint set on twelve unitary matrices.

Seek a self-adjoint **trace polynomial** `P` in the twelve unitary variables,
and constants `C,c>0`, such that

```text
P_n(U) + C * sum_{r in T_St} ||r(U)-I||_2^2  >= 0          (MATRIX)
```

for every `n` and every twelve-tuple `U in U(n)^12`, while for the canonical
group trace of the explicit atlas quotient `Gamma_St`,

```text
P_Gamma(lambda(g_1),...,lambda(g_12)) <= -c.               (GROUP)
```

Here `P_n(U)` means the scalar obtained by evaluating the formal normalized
traces in `P` with `tr_n`.  The relator penalty itself is a trace polynomial,
since

```text
||r(U)-I||_2^2 = tr_n((r(U)-I)^*(r(U)-I)).
```

**If such a certificate exists, `Gamma_St` is nonhyperlinear immediately.**
A hyperlinear microstate sequence with regular/canonical trace has relator
penalty tending to zero and every fixed trace word converging to its canonical
group trace.  Taking limits in `(MATRIX)` contradicts `(GROUP)`.

This is a radically different endpoint from the existing atlas work: no object
is rounded, no exact representation is recovered, and no stability statement
is needed.  One proves a dimension-free inequality that finite matrices obey
but the canonical group factor does not.

### 8. Why this is not the rejected dimension-free Nullstellensatz dream

A recent divergent-strategies dossier correctly rejected the vague hope
"analytic smallness forces an exact finite algebraic model"; small complex
errors do not become exact merely by reducing modulo a prime, and matrix size
can escape every fixed-dimensional compactness argument.

The separator above asks for none of that.  It is direct Hahn--Banach geometry:
the canonical moment point is to be separated from the closure of matricial
moment points by one finite-degree trace functional, with an explicit robust
relator penalty.  It can be true even when no approximate matrix tuple is close
to any exact finite-dimensional representation.

### 9. The crucial no-go: ordinary global tracial SOS is the wrong certificate language

There is an easy trap here.

Klep--Scheiderer--Volcic prove a Positivstellensatz for polynomials that are
trace-positive in **every tracial von Neumann algebra**.  Such a certificate
can never prove `(MATRIX)` together with `(GROUP)` for a group presentation:
`L(Gamma_St)` is itself a tracial von Neumann algebra in which the group
relators hold exactly.  Any inequality valid in all tracial von Neumann
algebras under those exact relations must hold in the canonical group model as
well, contradicting `(GROUP)`.

So the desired proof must be genuinely **matricial-only**.  It must use some
feature of finite-dimensional matrices (possibly through an all-dimensions
family of invariant-theoretic identities/inequalities) that is not a universal
tracial-von-Neumann-algebra positivity argument.

This boundary is conceptually aligned with the older Klep--Schweighofer
reformulation of Connes embedding: matrix trace positivity versus positivity in
all `II_1` factors is exactly where Connes embeddability lives.  After the
failure of Connes embedding, matrix-only trace inequalities that fail in a
tracial factor exist in principle.  The hard extra requirement here is to find
one whose violating tracial model is a **canonical group trace**, preferably
this explicit atlas group.

### 10. A computational-to-proof pipeline

1. **Canonical moment oracle.**  Choose a degree cutoff `D` and enumerate trace
   words in the twelve atlas generators.  Use the explicit presentation and
   the repository's word machinery/screens to evaluate as many canonical
   moments `tau_Gamma(w)` as can be certified (`0` unless the word is identity).

2. **Matrix moment relaxation.**  Use trace-polynomial SDP machinery to optimize
   linear functionals over unitary moment matrices with the atlas relator
   penalties included.  Increase degree and, separately, run direct numerical
   searches in concrete dimensions.  The goal is a stable separating
   functional, not a proof from a finite size sweep.

3. **Coefficient stabilization.**  Look for a low-degree rational pattern in
   the SDP dual certificate.  Prefer symmetrized words under obvious
   presentation automorphisms; symmetry can reduce thousands of relators to a
   few orbit-sums in the final inequality.

4. **All-dimensions proof.**  Prove the candidate inequality for every matrix
   size using finite-dimensional invariant theory, trace identities,
   Schur-complement/exterior-power inequalities, or a size-induction whose
   induction step is dimension free.  Procesi-style invariant theory is a
   natural language for reducing simultaneous-conjugation-invariant polynomial
   statements to traces of words.  Fixed-`n` trace Positivstellensatze can be
   used experimentally to discover the mechanism, but a final proof must
   survive arbitrary `n`.

5. **Adversarial factor check.**  Before celebrating any apparent SOS, verify
   that its proof is not actually valid in every tracial von Neumann algebra.
   If it is, it cannot separate the canonical atlas trace and some assumption
   has been smuggled in incorrectly.

### 11. What would count as a real breakthrough here

Even a certificate for a **truncated** atlas subsystem is valuable if it has an
all-dimensions proof and its group-trace evaluation is strictly negative after
adding only relations already certified in `T_St`.  Conversely, a theorem that
every low-degree trace polynomial satisfying the matrix inequality also holds
in the atlas group factor would rule out an entire degree range and prevent
wasted SDP scaling.

This program is therefore unusually falsifiable: each degree cutoff produces a
concrete convex separation problem, and every candidate inequality has an
explicit adversarial test in the group trace.

---

## III. Interaction between the programs without merging them

The two routes can help one another while remaining logically independent.

- The random-relator program can generate small-cancellation presentations that
  are deliberately chosen to maximize a numerical trace-moment separation
  score.  The probabilistic proof then remains a covering/return argument, not
  an SDP proof.
- The trace-separator program can use random presentations as a broad candidate
  generator if the atlas moment cone looks too close to matricial cones.
- Conversely, a low-degree matricial separator discovered empirically for
  random presentations may reveal what the entropy/return stratification is
  measuring (for example a hidden character or exterior-power statistic).

The important discipline is not to assume either route proves the other: a
finite-dimensional SDP sweep is not an all-`n` inequality, and absence of fixed
size exact representations is not a normalized-HS obstruction.

---

## Sources checked (primary sources)

- V. Pestov, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968.
  Theorem 3.6 gives the finite almost-homomorphism criterion with fixed
  separation; Remark 3.7 allows separation close to `sqrt(2)`.
- G. Kozma, A. Lubotzky, *Linear representations of random groups*,
  arXiv:1810.01529.  Fixed degree `d`: positive-density random groups have no
  nontrivial degree-`d` representations a.a.s.
- F. Bassino, C. Nicaud, P. Weil, *Generic properties of subgroups of free
  groups and finite presentations*, arXiv:1507.01088.  Generic
  small-cancellation in broad random-presentation models.
- N. Avni, I. Glazer, M. Larsen, *Fourier and small ball estimates for word
  maps on unitary groups*, arXiv:2402.11108.  Dimension-uniform HS small-ball
  estimates for fixed nontrivial word maps on `SU_n`, plus uniform smoothing
  after a word-dependent convolution power.
- E. Breuillard, B. Green, *Approximate groups, III: the unitary case*,
  arXiv:1006.5160.  Approximate subgroups of `U_n(C)` are almost abelian.
- E. Breuillard, B. Green, T. Tao, *The structure of approximate groups*,
  arXiv:1110.5008.  General finite-by-nilpotent structure of approximate
  groups.
- I. Klep, M. Schweighofer, *Connes' embedding conjecture and sums of hermitian
  squares*, arXiv:math/0607615; see also the correction arXiv:1303.3711.
  Algebraic trace-positivity reformulations of Connes embedding.
- I. Klep, V. Magron, J. Volcic, *Optimization over trace polynomials*,
  arXiv:2006.12510.  Trace-polynomial Positivstellensatz and SDP hierarchy.
- I. Klep, C. Scheiderer, J. Volcic, *Globally trace-positive noncommutative
  polynomials and the unbounded tracial moment problem*, arXiv:2205.05959.
  Global tracial Positivstellensatz -- useful here chiefly as the boundary
  showing why a universal tracial certificate cannot be the atlas separator.
- I. Klep, S. Spenko, J. Volcic, *Positive trace polynomials and the universal
  Procesi--Schacher conjecture*, arXiv:1702.01753.  Fixed-size matrix trace
  Positivstellensatze and invariant-theoretic certificate machinery.
- C. Procesi, *Tensor fundamental theorems of invariant theory*,
  arXiv:2011.10820.  Modern invariant-theoretic framework for equivariant
  polynomial maps on tuples of matrices.

## Deliberately not promoted as a new lane

K-theoretic/almost-flat-bundle ideas were checked and not promoted: this
repository already has extensive K0/K1/Exel--Loring/index nodes, and normalized
HS topology is especially hostile to naive Bott obstructions (e.g. Glebsky's
normalized-HS almost-commuting normal matrices are close to commuting ones,
arXiv:1002.3082).  That territory is neither novel here nor currently cleaner
than the two programs above.
