---
rg: 2
id: strebel-class-dz-is-locally-indicable-citation
kind: route
title: Import Strebel's class D(Z) and its identification with the locally indicable groups, as quoted by Cochran--Harvey
target: strebel-class-dz-is-locally-indicable
requires: []
artifacts:
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
---

Citation import, second hand. The source read was T. D. Cochran and S. Harvey,
*Homology and derived series of groups*, Geom. Topol. 9 (2005), 2159–2191,
arXiv math/0407203v2, pp. 2174–2175. TeX macros are stripped in the quote.

- **Lemma 4.4 and the paragraph after its proof:** "Lemma 4.4 Suppose f̃ : M → N is a
  homomorphism between free ZΓ–modules with Γ PTFA and let f = f̃ ⊗ id be the induced
  homomorphism of abelian groups M⊗_{ZΓ}Z → N⊗_{ZΓ}Z. [...] In [27, page 305], Strebel shows
  that, under the hypotheses of Lemma 4.4, if f is injective then f̃ is injective. There he
  shows that the class, D(Z), of groups Γ for which this property is satisfied includes
  torsion-free abelian groups and is closed under various natural operations such as
  extensions. Consequently, any PTFA group is in this class. This class of groups was
  previously called conservative and was later shown by J Howie and H Schneebli to coincide
  with the class of locally indicable groups [14]."
- **References:**
  - "[27] R Strebel, Homological methods applied to the derived series of groups, Comment.
    Math. Helv. 49 (1974) 302–332."
  - "[14] J Howie, H R Schneebeli, Homological and topological properties of locally
    indicable groups, Manuscripta Math. 44 (1983) 71–93."

**Reading.** `D(Z)` is defined by the property "`f` injective implies `f̃` injective" for
homomorphisms `f̃` of free `ZΓ`-modules. The PTFA hypothesis of Lemma 4.4 is used only to place
PTFA groups inside `D(Z)`. The quoted identification `D(Z) =` locally indicable is what the
target states.

**Trust surface.** Neither Strebel 1974 nor Howie–Schneebeli 1983 was read. The statement comes
from Cochran–Harvey, who use it as a black box.
- If the class in Strebel's paper is defined only for finitely generated free modules, the
  target still covers every use in the graph. The only consumer,
  `locally-indicable-groups-are-torus-surjunctive-proof`, applies it to `Z[G]^d` with `d`
  finite.
- The Fox witness of `fox-witness-kills-augmentation-torus-degree-proofs` is an independent
  consistency check. It shows that no group with a nontrivial finitely generated perfect
  subgroup lies in `D(Z)`, as the identification requires.
