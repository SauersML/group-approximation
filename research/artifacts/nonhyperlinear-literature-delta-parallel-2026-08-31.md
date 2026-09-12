# Nonhyperlinear discrete groups: parallel primary-source delta

Date cutoff: **2026-08-31 (UTC)**.

This is an independent theorem-level check of
`nonhyperlinear-literature-delta-2026-08-30.md`.  The acceptance criterion was
deliberately strict: a paper counts as closing `non-hyperlinear-group` only if
it proves, unconditionally, that a specified **discrete group** has no
asymptotically faithful models in finite-dimensional unitary groups for the
**normalized** Hilbert--Schmidt metric.  A non-CE trace, a non-CE groupoid or
equivalence-relation factor, a metric full group, a non-co-hyperlinear IRS, an
unnormalized-Frobenius obstruction, a nonsofic group, or a general nonlocal
game does not meet that criterion without an explicit group-level
embedding/separation theorem.

## Verdict

No unconditional nonhyperlinear discrete group was found.  No audited result
can honestly be imported to close the Cairn root `non-hyperlinear-group`.

The most current direct status statement is Chapter 3 of OpenAI's updated
[Ten Advances in Mathematics and Theoretical Computer
Science](https://cdn.openai.com/pdf/ten-proofs-oai.pdf) (updated 2026-08-06).
Its Theorem 1.1 proves that the unit group
`L_{F_2}(1,2)^times` of the binary Leavitt algebra is not sofic, but the same
chapter states that no nonhyperlinear discrete group is known and explicitly
says that its theorem does not decide whether that unit group is hyperlinear.
It also says that `MIP*=RE` does not produce a nonembeddable group von Neumann
algebra and that the known arithmetic Frobenius examples use the wrong,
unnormalized norm.  This agrees with the June 2026 status statement in
Dogon--Vigdorovich and the open-problem statement in Fournier-Facio's June
2026 revision.

The 2026 nonsofic breakthroughs therefore change the sofic boundary, not the
hyperlinear boundary:

```text
sofic  =>  hyperlinear
not sofic  -/->  not hyperlinear
```

The reverse implication is unavailable.  A proof of nonsoficity alone cannot
be promoted to normalized-HS separation.

## Exact group-level routes

### 1. Normalized-HS stability plus a central extension

[Dogon--Vigdorovich, arXiv:2506.20843v2, Theorem
1.3](https://arxiv.org/html/2506.20843v2) has an explicit discrete-group
endpoint and is the sharpest present conditional route.  Its hypotheses and
conclusion are:

- `Gamma` has property `(T;FD)`;
- there is a central extension
  `1 -> Z -> Gamma_tilde -> Gamma -> 1`;
- `Gamma_tilde` has finite abelianization; and
- `Gamma` is flexibly Hilbert--Schmidt stable in the paper's Definition 1.2,
  using normalized HS distance and allowing dimensions `D_n >= d_n` with
  `D_n/d_n -> 1` implicitly forced by convergence in the generalized metric.

Then there is an `N` such that
`Gamma_tilde/(N Z)`, a finite central extension of `Gamma`, is
nonhyperlinear.  This is a genuine group-level separation theorem, but it is
conditional on stability.  Question 1.4 asks for a modulus turning two
representations of `SL_2(Z)` that nearly agree on the Iwahori subgroup into
nearby representations that agree exactly.  Corollary 1.5 says a positive
answer gives a nonhyperlinear finite central extension of
`SL_2(Z[1/2])`.  No audited source answers Question 1.4.

Dogon's earlier [arXiv:2211.10492v3](https://arxiv.org/abs/2211.10492)
([arXiv DOI](https://doi.org/10.48550/arXiv.2211.10492)) gives the analogous
property-`(T)`/weak-ucp-or-flexible-HS route; in particular, flexible HS
stability of `Sp_{2g}(Z)` would imply existence of a nonhyperlinear group.
Again the stability hypothesis is not proved.

**Cairn action.**  Keep `dv-s-arithmetic-hs-stable-nonhyperlinear-extension`
and the Iwahori repair lane conditional.  The exact missing input is flexible
normalized-HS stability (equivalently the stated Iwahori gluing modulus for
the advertised `SL_2` candidate), not merely local stability, operator-norm
stability, or approximation by compressions.

### 2. New very-flexible stability does not overlap the obstruction hypotheses

[Fournier-Facio--Willett, arXiv:2603.18456v2, Theorems 1.1 and
1.2](https://arxiv.org/html/2603.18456v2)
([arXiv DOI](https://doi.org/10.48550/arXiv.2603.18456)) proves:

- LLP plus RFD lets every asymptotic representation be approximated by a
  compression of honest finite-dimensional representations; the theorem also
  applies to normalized HS and normalized Schatten norms; and
- finitely generated groups in the listed classes (fundamental groups of
  connected manifolds of dimension at most three, virtually free-by-cyclic
  groups, specified one-relator classes, limit groups, and RAAGs on chordal
  graphs) have LP and property FD, hence the stated very-flexible stability.

This does not close Dogon--Vigdorovich.  The paper does not assert that any of
those stable groups also satisfies the required property `(T;FD)` central-
extension hypotheses.  Indeed its Question 1.9 asks whether any infinite
property-`(T)` group (or group with relative `(T)` with respect to an infinite
subgroup) has LLP.  The paper also records that `SL_2(Z[1/p])` is residually
finite but not property FD.  Thus there is no theorem-level overlap to import
into the advertised central-extension candidate.

Corollary 7.6 and Remark 7.7 give the closest stronger overlap: LLP supplies a
ucp lift for every asymptotic representation, hence ucp stability and in
particular weak ucp stability in Dogon's sense.  This still leaves precisely
the missing rigidity hypothesis, because Question 1.9 leaves LLP open for
infinite property-`(T)` and relative-property-`(T)` groups.  Moreover the
very-flexible normalized-HS conclusion of Theorem 1.2/Corollary 7.12 imposes
no asymptotic dimension-ratio condition, so it is not the flexible HS
stability required by Dogon--Vigdorovich.  Remark 7.14 records actual HS
stability for some one-relator groups with center and for chordal RAAGs, but
neither class supplies the needed central-extension rigidity overlap.

### 3. Unnormalized Frobenius stability is a different metric

[Fournier-Facio, arXiv:2512.09180v2, Theorem
A](https://arxiv.org/html/2512.09180v2)
([arXiv DOI](https://doi.org/10.48550/arXiv.2512.09180)) embeds every countable
group, and every recursively presented group in the finitely presented case,
into a group `Gamma` with property `(T)` that is Frobenius stable but does not
have property `(T_2)`; in fact `H^2(Gamma;V) != 0` for every unitary
`Gamma`-representation `V`.  The paper defines its Frobenius norm as the
Euclidean norm inherited from `U(n) subset C^{n x n}` and explicitly calls the
Schatten norms in this result **unnormalized**.  It also states that
non-approximable groups are known in this unnormalized setting while the
hyperlinear approximation problem remains open.

For `A in M_n(C)`,

```text
||A||_F = sqrt(n) ||A||_(2,n).
```

Consequently a dimension-independent Frobenius obstruction may vanish after
normalization.  The theorem cannot be imported as normalized-HS stability or
as a nonhyperlinear construction.  This is a hard metric firewall for
`fournier-facio-universal-frobenius-stable-t-embedding-citation` and every
mixed-metric route.

## Game, algebra, and solution-group route

### What the primary sources actually give

1. [Ji--Natarajan--Vidick--Wright--Yuen,
   arXiv:2001.04383](https://arxiv.org/abs/2001.04383)
   ([arXiv DOI](https://doi.org/10.48550/arXiv.2001.04383)) proves
   `MIP*=RE` and thereby produces general non-CE tracial/game-algebra
   phenomena.  Its endpoint is not a discrete group carrying a separated
   canonical trace.
2. [Lin, arXiv:2510.07162](https://arxiv.org/abs/2510.07162)
   ([arXiv DOI](https://doi.org/10.48550/arXiv.2510.07162)) proves
   `MIP^co=coRE` and gives perfect-completeness gaps for general/synchronous
   nonlocal games.  It does not state that the games are LCS games and does
   not state a solution-group canonical-trace separation.
3. [Fanizza--Kroell--Mehta--Paddock--Rochette--Slofstra--Zhao,
   arXiv:2510.04943v4](https://arxiv.org/html/2510.04943v4)
   ([arXiv DOI](https://doi.org/10.48550/arXiv.2510.04943)) proves
   RE-hardness for strict commuting value in BCS games and a quantitative
   nested-conjugacy-to-BCS embedding.  The construction remains BCS, not LIN,
   and its main threshold is strict value above `1/2`; it supplies neither a
   perfect tracial/non-`R^U` LCS nor a nonhyperlinear solution group.
4. [Slofstra, arXiv:1606.03140v3, Theorem
   3.1](https://arxiv.org/html/1606.03140v3)
   ([JAMS DOI](https://doi.org/10.1090/jams/929)) says: if `G` is finitely
   presented, `J'` is a central involution, and `w_1,...,w_n` are specified
   involutions, then there is a solution group and an **injective**
   homomorphism sending `J'` to its distinguished central involution `J` and
   each `w_i` to a solution-group generator.  With `J'=1,n=0`, every finitely
   presented group embeds in a solution group.  This is a group embedding
   theorem, but using it for nonhyperlinearity requires a nonhyperlinear
   finitely presented source or a source element already known to vanish in
   all approximate normalized-HS representations.  It does not turn an
   arbitrary `MIP*=RE` bad trace into the regular trace of a group.
5. [Paddock--Slofstra, arXiv:2310.07901v2, Lemma 5.7 and Proposition
   5.8](https://arxiv.org/html/2310.07901v2)
   ([arXiv DOI](https://doi.org/10.48550/arXiv.2310.07901)) gives the exact
   closure criterion.  For an LCS `Ax=b`, tracial satisfiability is equivalent
   to `J != 1` in its solution group, while `R^U` satisfiability is equivalent
   to `J` being nontrivial in approximate normalized-HS representations.
   Hence a tracially satisfiable but non-`R^U` LIN system exists **iff** a
   finitely presented nonhyperlinear group exists.  This is an equivalence,
   not an independent construction.
6. [Taller--Vidick, arXiv:2507.22444v2](https://arxiv.org/html/2507.22444v2)
   ([arXiv DOI](https://doi.org/10.48550/arXiv.2507.22444)) proves LCS
   RE-hardness with completeness `1-epsilon`.  Its abstract explicitly says
   that achieving the same with `epsilon=0` would imply a nonhyperlinear
   group, and its introduction explains why a generic algebra-embedding
   reduction from BCS protocols to LCS protocols is unavailable.

### Exact missing seam

The usable group-level implication is already complete:

```text
finite LIN/LCS system
  + tracially satisfiable
  + not R^U-satisfiable
  => distinguished J is algebraically nontrivial
  + J vanishes in every normalized-HS approximate representation
  => its finitely presented solution group is nonhyperlinear.
```

What is absent is the first line's witness.  General perfect game gaps,
non-attainment in the NPA hierarchy, and positive-noise LCS hardness do not
supply it.  A source-specific compiler from the known perfect BCS/synchronous
gap to LIN would have to preserve the tracial model and rule out every
`R^U` model.  Paddock--Slofstra explicitly observes that a generic compiler of
this kind cannot be obtained merely from algebraic satisfiability.

**Cairn action.**  `lcs-tracial-ru-gap-equiv-nonhyperlinear` and
`perfect-lcs-gap-implies-nonhyperlinear` have the correct endpoint.  Keep
`mipstar-bcs-tracial-nonru-exists` category-specific.  No citation closes the
BCS-to-LIN/perfect-completeness seam.

## Trace, IRS, and groupoid firewalls

### Arbitrary non-CE traces do not control the canonical group trace

[Gao--Ioana--Vigdorovich, arXiv:2605.02242v1, Corollary
1.2](https://arxiv.org/html/2605.02242v1)
([arXiv DOI](https://doi.org/10.48550/arXiv.2605.02242)) proves that every
trace of the closed-surface/free groups denoted `Gamma_g^*` is a pointwise
limit of characters, so their trace simplex is Poulsen.  Immediately after
the corollary the paper notes that some traces on these groups cannot be
approximated pointwise by finite-dimensional traces, as a consequence of the
failure of Connes embedding.  But free groups and closed orientable surface
groups are residually finite and therefore hyperlinear.  Thus a non-CE trace
on `C*(G)` can coexist with a hyperlinear **canonical** regular trace on the
same group.  Only separation of the delta trace, equivalently non-CE of
`L(G)` with its regular trace, proves that `G` is nonhyperlinear.

### Manzoor's IRS is not a point mass

[Manzoor, arXiv:2502.06697v2](https://arxiv.org/html/2502.06697v2)
([arXiv DOI](https://doi.org/10.48550/arXiv.2502.06697)) proves existence of a
non-co-hyperlinear IRS on every nonabelian free group and a non-CE
equivalence-relation von Neumann algebra.  The decisive exact statements are:

- Theorem 2.7's non-co-sofic IRS need not be a point mass; the paper explicitly
  says this is why it does not prove a nonsofic group.
- Proposition 2.17(2) says that for a point mass `H=delta_N`, co-hyperlinearity
  is equivalent to hyperlinearity of the quotient `Gamma/N`.
- The constructed non-co-hyperlinear IRS is not proved to be such a point
  mass.
- At the end, the paper observes that non-CE of the equivalence-relation
  algebra is equivalent to metric nonhyperlinearity of the full group, but
  warns that the underlying discrete group may still be hyperlinear and asks
  whether the metric can be dropped.

Therefore no normal subgroup `N` and no nonhyperlinear quotient is produced.
This cannot close the root without a point-mass or canonical-Haar
groupification theorem.

## 2026 nonsofic and centralizer results

### Nonsofic groups are not normalized-HS counterexamples

- OpenAI, [Chapter 3, Theorem
  1.1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf):
  `L_{F_2}(1,2)^times` is nonsofic; its hyperlinearity is explicitly left
  undecided.
- [Fournier-Facio, arXiv:2608.02025v2, Theorem
  1.3](https://arxiv.org/html/2608.02025v2)
  ([arXiv DOI](https://doi.org/10.48550/arXiv.2608.02025)):
  there exists a finitely presented torsion-free nonsofic group, chosen in
  the proof with property `(T)`.  Its obstruction is permutation/LEF and
  states no normalized-HS separation; property `(T)` does not change that
  metric mismatch.
- [Kun--Thom, arXiv:2608.06222v1, Theorem
  A](https://arxiv.org/html/2608.06222v1)
  ([arXiv DOI](https://doi.org/10.48550/arXiv.2608.06222)):
  if `Gamma<G` is infranormal but not normal and both groups have property
  `(T)`, then `(direct_sum_{G/Gamma} Z/2) semidirect G` is nonsofic.  Theorem E
  provides explicit residually finite Kazhdan pairs satisfying the hypotheses.
  The proof is permutation-centralizer/fixed-algebra rigidity, not a unitary
  normalized-HS theorem.

These results validate closing `wreath-not-sofic`, not
`non-hyperlinear-group`.

The OpenAI chapter does isolate one logically valid direct attack on its
Leavitt unit-group candidate.  The Kervaire--Laudenbach property says that a
one-variable equation over a group whose total exponent in the variable is
nonzero has a solution in some overgroup.  The cited theorem of
Nitsche--Thom, [*Universal solvability of group equations*,
arXiv:1811.07737v2](https://arxiv.org/abs/1811.07737)
([journal DOI](https://doi.org/10.1515/jgth-2019-0167)), says every
hyperlinear group has this property.  Therefore an
explicit Kervaire--Laudenbach counterexample equation with coefficients in
`L_{F_2}(1,2)^times` would prove that group nonhyperlinear.  The chapter does
not supply such an equation and says the question is open.  This is a valid
new candidate lane, not a completed construction.  By contrast, the formal
Leavitt relations `t_i s_j=delta_(ij)` and
`s_0 t_0+s_1 t_1=1` occur in the ring; the nonunits `s_i,t_i` are not group
elements, so those relations cannot themselves serve as group equations.

### The exact unitary centralizer theorem remains an open problem

[Alekseev--Thom, arXiv:2608.05362v1, Open Problem
6.2](https://arxiv.org/html/2608.05362v1)
([arXiv DOI](https://doi.org/10.48550/arXiv.2608.05362)) precisely isolates the
missing unitary analogue.  Given a Kazhdan group `G`, a finite symmetric
generating set `S`, and a homomorphism

```text
pi : G -> U(prod_U M_(d_n)(C)),
```

part (a) asks whether, after replacing `d_n` by `m_n` with
`m_n/d_n ->_U 1`, the relative commutant can be written exactly as
`prod_U A_n` for finite-dimensional star-subalgebras
`A_n subset M_(m_n)(C)`.  Part (b) asks whether the `A_n` can be the exact
finite-level centralizers of lifts of the generators `pi(s)`.

This is direct primary-source confirmation that the unitary relative-
commutant exactification needed by `kt-centralizer-normalization-hs` is not a
theorem in the 2026 permutation-centralizer papers.  It also suggests a sharper
staging of that Cairn goal: solve 6.2(a), then 6.2(b), then prove that the
resulting coordinate centralizer is normalized under the relevant ambient
compressors.

[De Bondt--Thom, arXiv:2607.19556v1](https://arxiv.org/html/2607.19556v1)
([arXiv DOI](https://doi.org/10.48550/arXiv.2607.19556)) does not solve this:

- Proposition 4.3 classifies product-form isomorphisms of **whole** normalized-
  HS reduced products and forces the dimension ratio to tend to one;
- Theorem 4.4 shows arbitrary whole-product isomorphisms recognize coordinates
  and induce ultraproduct isomorphisms; and
- Theorem 4.5 classifies all such isomorphisms only under
  `OCA + MA_(aleph_1)(sigma-linked)`.

None of these statements identifies `pi(G)'` for an embedded group with an
ultraproduct of finite-level centralizers, and none proves its normalization by
a larger embedded group.  Whole-ambient rigidity is not relative-commutant
rigidity.

### Amenable quantum-group stability does not reach the candidates

[Brannan--Matsuda--Seguin, arXiv:2608.26362v1](https://arxiv.org/abs/2608.26362)
([arXiv DOI](https://doi.org/10.48550/arXiv.2608.26362)) proves representation
stability for compact and amenable discrete quantum groups and a compression
result for general amenable locally compact quantum groups.  It does not state
flexible normalized-HS stability for the nonamenable property-`(T)` or
property-`(T;FD)` discrete groups in the central-extension program.  It cannot
discharge Dogon--Vigdorovich's hypothesis.

## What can and cannot be imported into Cairn

| Cairn target | Source-checked import | Closure status |
|---|---|---|
| `non-hyperlinear-group` | Current status statement and false-positive firewalls | **Open**; no unconditional witness |
| `dv-s-arithmetic-hs-stable-nonhyperlinear-extension` | Dogon--Vigdorovich Theorem 1.3 with exact hypotheses | Conditional theorem already correct; stability/Iwahori gate open |
| Iwahori gluing lane | Dogon--Vigdorovich Question 1.4 and Corollary 1.5 | Open |
| `lcs-tracial-ru-gap-equiv-nonhyperlinear` | Paddock--Slofstra Lemma 5.7 and Proposition 5.8 | Equivalence closed; witness existence open |
| `perfect-lcs-gap-implies-nonhyperlinear` | Taller--Vidick explicitly identifies `epsilon=0` as sufficient | Conditional implication closed; perfect LCS gap open |
| `mipstar-bcs-tracial-nonru-exists` | MIP*, MIPco, and BCS results remain game/algebra statements | Must not be promoted to LIN/group without a compiler |
| `kt-centralizer-normalization-hs` | Alekseev--Thom Open Problem 6.2 gives the exact missing finite-level centralizer lift | Open; De Bondt--Thom does not close it |
| `wreath-not-sofic` | Kun--Thom Theorem A (with Theorem E examples) | Source-level nonsofic claim closed; no hyperlinear consequence |
| Leavitt unit-group candidate | OpenAI Chapter 3; failure of Kervaire--Laudenbach would obstruct hyperlinearity | Open; no failing equation is known |
| canonical-trace firewall claims | Gao--Ioana--Vigdorovich plus Manzoor | Strengthened as negative boundary; no group witness |

The only genuinely actionable new import for the normalized-HS program is
therefore **problem sharpening**, not root closure:

1. formulate the commutant lane explicitly around Alekseev--Thom Open Problem
   6.2(a)/(b), rather than treating permutation centralizer rigidity or
   whole-reduced-product rigidity as if it supplied the lift; these are two
   proposed stages, not a proved implication from part (a) to part (b);
2. make perfect `epsilon=0` LIN completeness, or a trace-preserving
   BCS-to-LIN compiler that also preserves non-`R^U` satisfiability, the only
   admissible game-theoretic missing input;
3. reject every construction that supplies only a non-CE trace, non-point-mass
   IRS, groupoid factor, or metric full group until it identifies a discrete
   quotient's canonical trace; and
4. reject unnormalized Frobenius and permutation/Hamming obstructions unless a
   source proves a dimension-uniform passage to normalized HS; and
5. for the new Leavitt candidate, search for an actual one-variable equation
   of nonzero exponent sum with no solution in any overgroup, rather than
   treating the ambient ring's one-sided inverses as group relations.

## Citation/version checklist

| Identifier | Version checked | Theorem/status used |
|---|---:|---|
| OpenAI, *Ten Advances*, Chapter 3 | updated 2026-08-06 | Theorem 1.1; explicit hyperlinearity status |
| [arXiv:2506.20843](https://doi.org/10.48550/arXiv.2506.20843) | v2, 2026-06-23 | Definition 1.2; Theorem 1.3; Question 1.4; Corollary 1.5 |
| [arXiv:2211.10492](https://doi.org/10.48550/arXiv.2211.10492) | v3, 2023-08-25 | conditional property-`(T)` central-extension route |
| [arXiv:2603.18456](https://doi.org/10.48550/arXiv.2603.18456) | v2, 2026-04-17 | Theorems 1.1--1.2; Questions 1.9--1.10 |
| [arXiv:2512.09180](https://doi.org/10.48550/arXiv.2512.09180) | v2, 2026-06-08 | Theorem A; unnormalized metric definition |
| [arXiv:2001.04383](https://doi.org/10.48550/arXiv.2001.04383) | current arXiv record | `MIP*=RE`; no group endpoint |
| [arXiv:2510.07162](https://doi.org/10.48550/arXiv.2510.07162) | current arXiv record | `MIP^co=coRE`; general games |
| [arXiv:2510.04943](https://doi.org/10.48550/arXiv.2510.04943) | v4, 2025-12-18 | BCS/nested-conjugacy embedding; NPA nonattainment |
| [arXiv:1606.03140](https://doi.org/10.48550/arXiv.1606.03140) | v3, 2020-09-27 | Theorem 3.1 |
| [arXiv:2310.07901](https://doi.org/10.48550/arXiv.2310.07901) | v2, 2025-01-15 | Lemma 5.7; Proposition 5.8 |
| [arXiv:2507.22444](https://doi.org/10.48550/arXiv.2507.22444) | v2, 2026-04-01 | LCS completeness `1-epsilon`; explicit `epsilon=0` boundary |
| [arXiv:2502.06697](https://doi.org/10.48550/arXiv.2502.06697) | v2, 2026-04-04 | Theorem 2.7; Proposition 2.17; metric/discrete warning |
| [arXiv:2605.02242](https://doi.org/10.48550/arXiv.2605.02242) | v1, 2026-05-04 | Corollary 1.2 and post-corollary non-CE-trace observation |
| [arXiv:2608.02025](https://doi.org/10.48550/arXiv.2608.02025) | v2, 2026-08-14 | Theorem 1.3, torsion-free nonsofic group |
| [arXiv:2608.06222](https://doi.org/10.48550/arXiv.2608.06222) | v1, 2026-08-06 | Theorems A and E |
| [arXiv:1811.07737](https://doi.org/10.48550/arXiv.1811.07737) | v2, 2021-09-23 | hyperlinear-group solvability of Kervaire--Laudenbach equations |
| [arXiv:2608.05362](https://doi.org/10.48550/arXiv.2608.05362) | v1, 2026-08-05 | Open Problem 6.2(a)--(b) |
| [arXiv:2607.19556](https://doi.org/10.48550/arXiv.2607.19556) | v1, 2026-07-21 | Proposition 4.3; Theorems 4.4--4.5 |
| [arXiv:2608.26362](https://doi.org/10.48550/arXiv.2608.26362) | v1, 2026-08-26 | amenable/compact quantum-group stability abstract |

Where a journal DOI was useful and source-verified, the Slofstra embedding
paper is [JAMS 33 (2020), DOI 10.1090/jams/929](https://doi.org/10.1090/jams/929).
All other DOI links above are arXiv-issued DataCite identifiers and point to
the exact cited preprint records.
