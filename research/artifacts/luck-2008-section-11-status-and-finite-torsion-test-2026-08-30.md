# Lück 2008, Section 11: 2026 status audit and a finite torsion test

## Scope and source discipline

The source is Wolfgang Lück, *Survey on geometric group theory*,
arXiv:0806.3771v2 (11 September 2008), §11.  The list contains seven
hyperbolic-group questions, three isomorphism-conjecture questions, and four
quasi-isometry questions.  The status audit below uses theorem papers or
current statements by authors working on the relevant conjecture; search
snippets, encyclopedias, and crowd-edited status pages are not treated as
evidence.

The audit found no basis for declaring any **entire numbered item** newly
settled in its full generality.  It did find components of 11.2(i) solved
since 2008; those are recorded and excluded from the proof search.

## Status table

| Lück item | 2026 disposition | Audit boundary |
|---|---|---|
| 11.1(i), every hyperbolic group virtually torsion-free | **Open; attacked here** | Recent work still explicitly calls this open.  The theorem below gives an exact finite-quotient obstruction, not a solution. |
| 11.1(ii), residual finiteness | **Open; skipped as already represented in Cairn** | `non-residually-finite-hyperbolic-group` and its audit already track this.  Current 2025--26 papers continue to call Gromov's question open. |
| 11.1(iii), the `S^2` boundary/Cannon conjecture | **Open; skipped** | No unconditional Cannon theorem was found.  Recent boundary papers continue to use additional analytic or cubulation hypotheses. |
| 11.1(iv)--(v), homology-sphere/sphere boundaries and manifold realization | **Partly settled already in Lück's source; otherwise open; skipped** | Lück's Theorem 7.4 gives the high-dimensional statement (`n>=6`) under its stated torsion-free hypotheses.  The low-dimensional/general realization questions must not be marked solved by that theorem. |
| 11.1(vi), characterize hyperbolic boundaries | **Open-ended classification problem; skipped** | Later realization and rigidity theorems provide classes, not a classification of all boundary homeomorphism types. |
| 11.1(vii), every hyperbolic group CAT(0) | **Open; skipped** | Haettel's 2025 theorem paper still describes this as a famous open problem while producing a different geometric model. |
| 11.2(i), Baum--Connes/Farrell--Jones/Borel for `SL_n(Z)`, mapping class groups, `Out(F_n)` | **Some components solved; bundled item open** | Kammeyer--Lück--Rüping prove full K- and L-theoretic Farrell--Jones for arbitrary lattices in virtually connected Lie groups, covering `SL_n(Z)`.  Bartels--Bestvina prove Farrell--Jones for mapping class groups.  Lück's 2026 status survey still lists `Out(F_n)`, `n>=3`, as open for the Full Farrell--Jones Conjecture.  The remaining Baum--Connes portions are not erased by these algebraic K/L-theory results. |
| 11.2(ii), Farrell--Jones/Borel for amenable groups | **Open in general; skipped** | Lück's 2026 survey lists amenable (indeed even elementary amenable in the full formulation used there) among the open classes; known virtually-solvable results are only a subclass. |
| 11.2(iii), seek a property beyond the known isomorphism-conjecture classes | **Exploratory rather than a single yes/no conjecture; skipped** | The 2026 Farrell--Jones survey explains that expander and other exotic properties occur among groups satisfying FJ, with no current counterexample strategy. |
| 11.3(i), finitely presented quasi-isometric pair, one solvable and one not | **Open; skipped** | The classical non-virtually-solvable partner is not finitely presented; no primary theorem settling the finitely presented version was found. |
| 11.3(ii), virtual polycyclicity under quasi-isometry | **Open in general; skipped** | The general rigidity statement continues to be posed as a conjecture; many geometric subclasses are known. |
| 11.3(iii), Mal'cev completion under quasi-isometry | **Open; skipped** | Llosa Isenrich--Pallier--Tessera (2023) explicitly retain the conjectural classification; their examples separate asymptotic-cone equivalence from quasi-isometry rather than refute the conjecture. |
| 11.3(iv), Novikov--Shubin invariants / vanishing of `L^2`-torsion | **Open in the stated generality; skipped** | Sauer's theorem proves the Novikov--Shubin statement for amenable groups, already noted by Lück; that positive class is not the unrestricted assertion. |

## New theorem: the finite torsion carrier criterion

Let `G` admit finite subgroups `F_1,...,F_r` such that every finite subgroup
of `G` is conjugate into one of them.  Then the following are equivalent:

1. `G` is virtually torsion-free;
2. the finite residual `R_f(G)` is torsion-free;
3. `R_f(G) intersect F_i={1}` for every `i`;
4. one finite quotient of `G` is injective on every `F_i`;
5. `G` has a normal torsion-free subgroup of finite index.

The full proof is in `finite-torsion-carrier-criterion-proof`.  The delicate
direction is (3) to (4): it uses finiteness of the union of the nonidentity
elements of the `F_i`, chooses one finite quotient per element from the
definition of the finite residual, and takes their finite direct product.
No residual-finiteness hypothesis is used.

Lück's Theorem 7.2(v)(d) states that a hyperbolic group has finitely many
conjugacy classes of finite subgroups.  The criterion therefore gives the
exact reformulation

```text
every hyperbolic group is virtually torsion-free
  <=> the finite residual of every hyperbolic group is torsion-free.
```

It also supplies a sharp negative certificate: a counterexample is exactly a
hyperbolic group having a finite-order element killed by every homomorphism
to a finite group.  This is weaker than constructing a group with no
nontrivial finite quotients and strictly weaker than disproving residual
finiteness.

## Prime-order and normal-closure sharpening

The finite carrier can be reduced further.  A subgroup contains torsion if
and only if it contains an element of prime order.  Hence it suffices to
choose representatives `P_1,...,P_s` of the finitely many conjugacy classes
of prime-order subgroups and find one finite quotient which is nontrivial
(equivalently injective) on every `P_j`.  This is still equivalent to virtual
torsion-freeness, but removes all composite-order and redundant carrier
tests.

There is also a geometric dichotomy for a failed test.  Let `R` be the
finite residual of a non-elementary hyperbolic group, let `E` be its maximal
finite normal subgroup, and take a prime-order `x in R`.  Its normal closure
lies in `R`.  If that closure is finite, then `x in E`; the finite conjugation
map `G->Aut(E)` kills `R`, so `x in Z(E)`.  If the closure is infinite, the
standard normal-subgroup boundary theorem makes it non-elementary with full
limit set, and it contains a nonabelian free subgroup.

Thus every counterexample has one of two sharply different forms:

```text
prime torsion in R intersect Z(E),
or a prime-torsion-generated non-elementary normal subgroup inside R.
```

In particular, when `E={1}`, a counterexample cannot have an elementary,
free-subgroup-free, or amenable finite residual.  Under any of those smallness
hypotheses the residual is actually trivial, so the group is residually
finite.  This is a new sufficient class, not a solution of Lück 11.1(i): an
arbitrary finite residual need not satisfy a smallness hypothesis, and the
central finite-radical alternative is not eliminated.

## Primary/current sources

- W. Lück, *Survey on geometric group theory*, arXiv:0806.3771v2,
  especially Theorem 7.2(v)(d), Theorem 7.4, and §11:
  https://arxiv.org/abs/0806.3771
- H. Kammeyer, W. Lück, H. Rüping, *The Farrell-Jones conjecture for
  arbitrary lattices in virtually connected Lie groups*:
  https://arxiv.org/abs/1401.0876
- A. Bartels, M. Bestvina, *The Farrell-Jones Conjecture for mapping class
  groups*: https://arxiv.org/abs/1606.02844
- W. Lück, *Survey on the Farrell-Jones Conjecture* (2026 status survey),
  arXiv:2507.11337: https://arxiv.org/abs/2507.11337
- C. Llosa Isenrich, G. Pallier, R. Tessera, *Cone-equivalent nilpotent
  groups with different Dehn functions*: https://arxiv.org/abs/2008.01211
- T. Haettel, *ell-p metrics on cell complexes*, including the current
  CAT(0) status statement: https://doi.org/10.1112/jlms.70062
- N. Andrew, Y. Guerch, S. Hughes,
  *Automorphisms of relatively hyperbolic groups and the Farrell--Jones
  conjecture*, including the one-ended torsion case and the remaining
  infinitely-ended boundary:
  https://arxiv.org/abs/2311.14036
