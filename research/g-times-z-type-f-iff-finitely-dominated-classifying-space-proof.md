---
rg: 2
id: g-times-z-type-f-iff-finitely-dominated-classifying-space-proof
kind: route
title: "Prove the dictionary for Problem 1.21: homotopy retract, Wall's theorem, Mather's trick and the syzygy argument"
target: g-times-z-type-f-iff-finitely-dominated-classifying-space
requires: []
---

Notation: a CW complex `Y` is *finitely dominated* if there are a finite CW
complex `K` and maps `f : Y → K`, `g : K → Y` with `g ∘ f ≃ id_Y`. Type F
means that some `K(G,1)` is a finite CW complex.

Two classical theorems are used, quoted from S. Ferry and A. Ranicki, *A
survey of Wall's finiteness obstruction*, arXiv:math/0008070 (TeX source
`ferran.tex` read on MSI, 2026-09-13):

- **Wall's theorem**, Ferry–Ranicki Theorem 3.1 (Wall, Ann. of Math. 81
  (1965); Proc. Roy. Soc. A 295 (1966)). (i) "A finitely dominated space X
  has a finiteness obstruction [X] ∈ K̃_0(Z[π_1(X)]) such that [X] = 0 if
  and only if X is homotopy equivalent to a finite CW complex." (iii) "A CW
  complex X is finitely dominated if and only if π_1(X) is finitely presented
  and the cellular Z[π_1(X)]-module chain complex C_*(X̃) of the universal
  cover X̃ is chain homotopy equivalent to a finite chain complex 𝒫 of f.g.
  projective Z[π_1(X)]-modules." Section 3 of the survey computes `[X]` from
  any such `𝒫` as the Euler class `Σ_i (−1)^i [P_i]`, up to a global sign
  convention that does not affect vanishing.
- **Mather's trick**, Ferry–Ranicki Proposition 1.5 (Mather, *Counting
  homotopy types of manifolds*, Topology 3 (1965)): "A topological space X is
  finitely dominated if and only if X × S^1 is homotopy equivalent to a
  finite CW complex."

The same dictionary between `K̃_0(ZG)` and finite domination is recorded in
W. Lück and H. Reich, *The Baum–Connes and the Farrell–Jones conjectures in
K- and L-theory*, arXiv:math/0402405, subsubsection "Finiteness
Obstructions", Theorem "Properties of the Finiteness Obstruction" and the
Consequence after it. Below, "Wall (a)" means Theorem 3.1(iii) and "Wall (b)"
means Theorem 3.1(i).

Throughout, `Y` denotes a `K(G,1)` CW complex. Any two are homotopy
equivalent, so finite domination does not depend on the choice.

**(1) ⇔ (2)** is Mather's trick applied to `Y`, because `Y × S^1` is a
`K(G × Z, 1)`. The direction used most often is spelled out here; it is the
argument of the survey's converse.

**(1) ⇒ (2).** Let `X` be a finite `K(G × Z, 1)`. `Y × S^1` is a `K(G × Z,1)`,
so there is a homotopy equivalence `h : Y × S^1 → X` with homotopy inverse
`k`. Let `i : Y → Y × S^1`, `y ↦ (y, *)`, and let `p : Y × S^1 → Y` be the
projection, so `p ∘ i = id_Y`. Put `f = h ∘ i : Y → X` and
`g = p ∘ k : X → Y`. Then `g ∘ f = p ∘ (k ∘ h) ∘ i ≃ p ∘ i = id_Y`, so `Y` is
dominated by the finite complex `X`.

**(2) ⇒ (3).** By Wall's theorem (a), `G = π_1(Y)` is finitely presented, and
`C_*(Ỹ)` is chain homotopy equivalent to a finite complex `P_*` of finitely
generated projective `ZG`-modules. `Ỹ` is contractible, so `C_*(Ỹ)` is a free
resolution of `Z`. The chain homotopy equivalent complex `P_*` has the same
homology, and the augmentation transports, so `P_* → Z` is a finite resolution
by finitely generated projectives. Hence `G` is of type FP.

**(3) ⇒ (4).** Type FP gives type `FP_∞` and `cd G < ∞`. For `n ≥ 2`, a
finitely presented group of type `FP_n` is of type `F_n`, by induction on the
skeleton. Let `K` be an `(n−1)`-dimensional `K(G,1)`-skeleton with finitely
many cells and `(n−2)`-connected universal cover. Then `π_{n−1}(K) =
H_{n−1}(K̃) = ker(C_{n−1}(K̃) → C_{n−2}(K̃))` is the kernel at the end of a
partial resolution of `Z` by finitely generated free modules. It is finitely
generated because `G` is of type `FP_n`: by Schanuel's lemma this does not
depend on the partial resolution. Attaching finitely many `n`-cells along
generators kills it by Hurewicz. Starting from a finite presentation complex,
this gives a `K(G,1)` with finitely many cells in each dimension. See K. S.
Brown, *Cohomology of Groups*, GTM 87, Chapter VIII, Section 7.

**(4) ⇒ (3).** Type `F_∞` gives finitely presented and `FP_∞`. Let
`n = cd G`. If `n = 0` then `G = 1`. Otherwise take a resolution `F_* → Z`
by finitely generated free modules and put `K_n = ker(F_{n−1} → F_{n−2})`,
with `F_{−1} = Z`. Dimension shifting gives `Ext^1_{ZG}(K_n, M) ≅
Ext^{n+1}_{ZG}(Z, M) = 0` for every module `M`, so `K_n` is projective. It
is finitely generated, being the image of `F_n`. So
`0 → K_n → F_{n−1} → … → F_0 → Z → 0` is a finite resolution by finitely
generated projectives, and `G` is of type FP. See Brown, VIII.6.

**(3) ⇒ (2).** Build a `K(G,1)` `Y` with finitely many cells in each
dimension, using (3) ⇒ (4). `C_*(Ỹ)` is a resolution of `Z` by finitely
generated free modules. By the fundamental lemma of homological algebra it is
chain homotopy equivalent to the finite projective resolution given by type
FP. With `π_1 Y = G` finitely presented, Wall's theorem (a) makes `Y` finitely
dominated.

**(2) ⇒ (1).** By Mather's trick, `Y × S^1` is homotopy equivalent to a finite
CW complex. It is a `K(G × Z, 1)`, so `G × Z` is of type F.

**Torsion-freeness.** A nontrivial finite cyclic subgroup `C` has
`H^{2k}(C; Z) ≠ 0` for all `k ≥ 1`, so `cd C = ∞`. Cohomological dimension
does not increase on passing to subgroups (Brown, VIII.2). So `cd G < ∞`
forces `G` to be torsion-free.

**The obstruction.** Let `Y` be finitely dominated. By Wall's theorem (b),
`Y` is homotopy equivalent to a finite complex exactly when
`[Y] = Σ(−1)^i [P_i] = 0` in `K̃_0(ZG)`, for `P_*` as in (a). For a `K(G,1)`,
any finite projective resolution of `Z` is such a `P_*`. Two finite projective
resolutions of `Z` are chain homotopy equivalent, and chain homotopy
equivalent finite projective complexes have the same Euler class in
`K̃_0(ZG)`. So the class is `σ(G)` as defined in the target, independent of
the resolution. `G` is of type F exactly when some `K(G,1)` is finite, that is
exactly when `σ(G) = 0`.

**Problem 1.21.** The problem's hypothesis is (1). By the equivalences, the
problem asks whether every `G` satisfying (3) has `σ(G) = 0`. Equivalently:
is every finitely dominated aspherical CW complex homotopy equivalent to a
finite one? Aspherical CW complexes are exactly the `K(G,1)`s. QED
