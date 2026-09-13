---
rg: 2
id: burger-mozes-infinitely-transitive-tree-groups-citation
kind: route
title: Import Lemma 3.1.1, Propositions 1.2.1 and 3.1.2 of Burger-Mozes (local to global), and Section 5, Proposition 5.2 and Theorems 6.3-6.5 of Burger-Mozes (lattices)
target: burger-mozes-infinitely-transitive-tree-groups
requires: []
---

**Citation.** Read from the Numdam PDFs on 2026-09-13 (lane `ex-tree-lattice-mixing`).

*M. Burger, S. Mozes, Groups acting on trees: from local to global structure, Publ.
Math. IHÉS 92 (2000) 113–150.*

* p. 116, §1.1: "`H^(∞) := ∩ L` where the intersection is taken over all open subgroups
  `L < H` of finite index, and `QZ(H) = {h ∈ H : Z_H(h) is open}`."
* p. 117: "`H^(∞) = ∩_(N ◁ H) N`, where the intersection is taken over all closed,
  cocompact normal subgroups of `H`. Thus, every normal cocompact subgroup of `H`
  contains `H^(∞)`; at the other extreme, every discrete normal subgroup of `H` is
  contained in `QZ(H)`."
* p. 117, Proposition 1.2.1: "Let `H < Aut g` be a closed subgroup. We assume that `H` is
  non-discrete and locally quasiprimitive. 1) `H/H^(∞)` is compact. 2) `QZ(H)` acts
  freely on `X`; it is a discrete non cocompact subgroup of `H`. 3) For any closed normal
  subgroup `N ◁ H`, either `N` is non-discrete cocompact and `N > H^(∞)` or `N` is
  discrete and `N ⊂ QZ(H)`."
* p. 141, Lemma 3.1.1: "For a closed subgroup `H < Aut T`, the following are equivalent:
  (1) `H` is locally `∞`-transitive. (2) `H(x)` is transitive on `T(∞)`, `∀x ∈ X`.
  (3) `H` is non-compact and transitive on `T(∞)`. (4) `H` is 2-transitive on `T(∞)`.
  Any of these properties imply, (5) `H(x) < Sym E(x)` is 2-transitive and `H` is
  non-discrete."
* p. 142, Proposition 3.1.2: "Let `T` be a locally finite tree and `H < Aut T` a closed,
  locally `∞`-transitive group. Then, (1) `QZ(H) = (e)`. (2) `H^(∞)` is locally
  `∞`-transitive and topologically simple."
* p. 115, §0.1 (same text as the lattices paper, p. 153): "`F` is 2-transitive `⇒` `F` is
  primitive `⇒` `F` is quasiprimitive."

*M. Burger, S. Mozes, Lattices in product of trees, Publ. Math. IHÉS 92 (2000)
151–194.*

* p. 178, §5: "When `F < S_d` is 2-transitive we have (see [B-M]_3 3.1, 3.2) (1)
  `U(F)^+ = U(F)^(∞)` is of index 2 in `U(F)` and simple. (2) `U(F)^+` is locally
  `∞`-transitive."
* p. 178, Proposition 5.2: "Assume that the permutation groups `P_h`, `P_v` are
  2-transitive and that `L_h`, `L_v` are simple non-abelian. Then ... (2) If
  `(a_h, a_v) = (d_h − 1, d_v − 1)`, the lattice `Γ` is irreducible and
  `Γ < U(P_h) × U(P_v)` has dense projections." Its proof (p. 179) shows that `a_h = 0`
  forces `Γ` reducible, so an irreducible `Γ` is in case (2).
* p. 187, Theorem 6.3 and its proof: `P_h = A_(2n)`, `P_v = A_(2m)`, and "the
  monomorphism `A_(13,17) ↪ X` implies that `X = Γ\(T_(2n) × T_(2m))` is irreducible, and
  hence (Proposition 5.2) `Γ < U(A_(2n)) × U(A_(2m))` has dense projections".
* p. 187, Theorem 6.4, proof: with `^(1)X = A_(13,17) ⊠ A_(13,17)`, whose fundamental
  group is not residually finite and injects into `π_1(X)`, all conditions of
  Corollary 5.4 hold, so `π_1(X)` is virtually simple.
* p. 187, Theorem 6.5: "Let `Z` be a 1-vertex, VH-T-complex. Then there exists a 1-vertex
  VH-T-complex `X` such that: (1) `Z` embeds into `X`, (2) `π_1(X)` is virtually simple.
  In particular, `π_1(Z)` is isomorphic to a subgroup of `π_1(X)`." Proof: "Applying
  Proposition 6.2, we may assume that `P_h^Z` and `P_v^Z` consist of even permutations.
  We apply then Proposition 6.1 to the case `n = 2`, `^(0)X = A_(13,17)`,
  `^(1)X = A_(13,17) ⊠ A_(13,17)`, `^(2)X = Z`, `k = ℓ = 4` and argue as in Theorem 6.4."
* p. 184, Proposition 6.1(3a): if `d_h > 2·^(0)d_h` and all `^(i)P_h` consist of even
  permutations, then `P_h` is the alternating group `A_(d_h)`.

So in Theorem 6.5, `X` contains the non-residually-finite `^(1)X`, hence is irreducible
(reducible lattices are commensurable with products of free groups, p. 152). With
`P_h = A_(2n)` and `P_v = A_(2m)`, the argument of Theorem 6.3 through Proposition 5.2(2)
gives dense projections in `U(A_(2n)) × U(A_(2m))`. This is the content of item 5.
