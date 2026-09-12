# Published nonhyperlinear shortcut audit — 2026-08-21

This audit checked primary sources current through 2026-08-21 for three direct
closures: a finitely presented normalized-HS-stable group with nontrivial
finite residual, a perfect `qc` versus `qa` LCS/toric gap, and a theorem
robustifying exact finite-dimensional invisibility.  No such closure was found.
The precise stopping points are below.

## 1. Stability plus finite residual

- Dogon--Vigdorovich, arXiv:2506.20843v2, Definition 1.2 and Theorem 1.3,
  use **flexible normalized-HS stability** (called HS stability in their
  convention), property `(T;FD)`, and an infinite central extension with
  finite abelianization to produce a nonhyperlinear finite central extension.
  Their Corollary 1.5 is conditional on the still-open Iwahori repair Question
  1.4 for `SL_2(Z[1/2])`.
- Dogon--Vidick, arXiv:2607.20135v1, prove polynomial HS stability for the
  lamplighter group.  That group is amenable/residually finite and is not
  finitely presented, so it has no nontrivial finite residual and does not meet
  the closure hypothesis.
- Spaas, arXiv:2603.02058v1, proves HS stability for graph products of abelian
  groups on chordal graphs, including chordal right-angled Artin groups.  The
  finitely generated instances are residually finite, so again no marked finite
  residual is supplied.
- Fournier-Facio--Gerasimova--Spaas, arXiv:2307.13155v2, do give
  non-residually-finite **locally** HS-stable groups, but explicitly state that
  their examples are not HS-stable.  Their property `(T)` theorem is an
  obstruction: an infinite hyperlinear property-`(T)` group is not even
  locally HS-stable.

Thus the published stable examples checked here live on the residually finite
side, while the published non-residually-finite examples have only the weaker
local stability which cannot exactify a canonical microstate sequence.

There is no finite-presentation loophole in that last sentence.
Fournier-Facio--Gerasimova--Spaas, arXiv:2307.13155v2, Lemma 3.11, prove
that local and global stability coincide for finitely presented groups, for
arbitrary metric targets and also in the flexible variants.  Consequently
their non-RF locally HS-stable but non-HS-stable examples are automatically
not finitely presented.  Conversely, any finitely presented non-RF locally
HS-stable example would already be nonhyperlinear by
`finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear`.

## 2. Perfect commuting versus matrix game gaps

- Lin, arXiv:2510.07162v1, Theorem 6.15 and its proof paragraph, gives finite
  synchronous games in the separated promise class

  ```text
  omega_co(G)=1,  omega_*(G)<=1/2.
  ```

  This freezes the adversarial source into one finite game, but the theorem
  does not put that game in LCS or phase-safe toric solution-group syntax.
- Taller--Vidick, arXiv:2507.22444v2, prove the LCS gap with completeness
  `1-epsilon`, for every sufficiently small positive `epsilon`.  Their abstract
  explicitly states that the `epsilon=0` upgrade would imply a nonhyperlinear
  group.  Thus the required perfect LCS case remains open in the latest version.
- Cleve--Culf--Taller, arXiv:2607.06876v1, Theorems 4.2--4.3, reduce those LCS
  games to tilted XOR games with completeness `3/4-epsilon` and a constant
  soundness gap.  Section 1 also notes that a binary game has a perfect quantum
  strategy iff it has a perfect classical one.  This is a strong new hardness
  theorem, not a perfect nonclassical group signal.
- Culf, arXiv:2603.14746v1, turns `1-epsilon` projection-game strategies into
  tracial strategies of value `1-O((L epsilon)^(1/4))`.  It is a rounding to a
  tracial strategy, not an exactification to a finite-dimensional group
  representation and not a perfect-completeness compiler.
- Culf--van Dobben de Bruyn--Zeman, arXiv:2604.01408v1, characterize robust
  commutativity gadgets by stable commutativity.  Their `qa` versus `qc`
  separation of gadget classes is explicitly conditional on the existence of
  a nonhyperlinear group, so it cannot be used as an unconditional source for
  one.

The published static synchronous gap is therefore available; the missing
published statement is still the phase-safe LCS/toric or ordinary-group
transducer with a fixed normalized-HS modulus.

## 3. Exact invisibility does not robustify automatically

Slofstra--Vidick, arXiv:1711.10676, Proposition 3.2, already supply a sharp
counterexample.  Their finitely presented group `K` is sofic and has a
nontrivial central involution `c` killed by every finite-dimensional
representation.  Therefore exact finite-dimensional invisibility, even plus
finite presentation and soficity, cannot imply normalized-HS collapse of
approximate representations.  This is wired as
`exact-fd-invisibility-has-no-general-hs-robustification`.

## Conclusion

The literature offers two clean conditional closures and one static source:

```text
flexible HS stability + finite-residual/central-extension mark
    => nonhyperlinear group;

perfect qc-vs-qa LCS or phase-safe toric gap
    => nonhyperlinear solution/game group;

Lin static synchronous gap
    + still-missing source-specific HS group transducer
    => nonhyperlinear group.
```

No checked primary source discharges the bold hypothesis in either of the
first two lines, and the Slofstra--Vidick example rules out discharging the
first merely from exact finite-dimensional invisibility.
