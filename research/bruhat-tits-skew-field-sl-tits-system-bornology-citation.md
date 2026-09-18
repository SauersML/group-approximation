---
rg: 2
id: bruhat-tits-skew-field-sl-tits-system-bornology-citation
kind: route
title: Bruhat-Tits I, Publ. IHES 41 (1972), 10.2 with 6.5, 8.1.7, 3.1.3 and 1.2.6-1.2.8
target: bruhat-tits-skew-field-sl-tits-system-bornology
requires: []
---

**Import, quoted verbatim** from F. Bruhat and J. Tits, *Groupes réductifs sur
un corps local. I. Données radicielles valuées*, Publ. Math. IHÉS 41 (1972)
5–251 (numdam file PMIHES_1972__41__5_0.pdf). Read at source on 2026-09-18 by
swarm-0917-w9-w9-bh-break from the numdam text layer. OCR damage to symbols is
repaired below; the words are the source's.

- Introduction, p. 12: "comme nous ne nous y bornons pas aux valuations
  discrètes et que les corps gauches de rang infini sur leur centre y sont
  admis".
- (1.2.6): "On appelle système de Tits un quadruplet (G, B, N, S) … (T 3) Pour
  tout s∈S et tout w∈W, on a sBw ⊂ BwB ∪ BswB."
- (1.2.7): "L'application w ↦ BwB est une bijection de W sur l'ensemble B\G/B
  des doubles classes de G suivant B".
- (1.2.8): "Soient s∈S et w∈W; les trois relations « BsBwB contient une seule
  double classe modulo B », BsB.BwB = BswB et l(sw) = l(w)+1 sont
  équivalentes".
- (3.1.3): "Soit ℬ l'ensemble des parties de G dont l'image canonique dans
  B\G/B est finie. Alors ℬ est une bornologie sur G compatible avec la loi de
  groupe de G." (3.1.4): "La bornologie ℬ introduite en (3.1.3) est dite
  définie par le système de Tits (G, B, N)."
- 6.5: "nous supposons en outre que la valuation φ est discrète." Théorème:
  "Soit G' le sous-groupe de G engendré par N' = ν^{-1}(W) et les U_a (a∈Φ).
  Posons T' = T∩N' et B = P̂_C. (i) On a B∩N' = H et N'/H = W. Le quadruplet
  (G', B, N', S) est un double système de Tits."
- (8.1.7): "On appelle bornologie définie par φ … la bornologie sur G image
  réciproque de la bornologie naturelle de Isom 𝓘 … On notera que, dans le cas
  où φ est discrète, cette bornologie coïncide avec celle définie par le système
  de Tits défini par φ (3.1.8)."
- (10.2.1): "Soit K un corps, non nécessairement commutatif, et soit X un
  espace vectoriel à droite de dimension finie ≥ 2 sur K".
- (10.2.2): G is "un sous-groupe de GL(X) contenant les sous-groupes U_a", and
  the group they generate "n'est autre que le sous-groupe SL(X) engendré par
  toutes les transvections de X (ou encore noyau du déterminant de Dieudonné)".
- (10.2.3): "Soit ω une valuation non impropre de K. … La famille φ^ω … est
  une valuation spéciale de la donnée radicielle".
- (10.2.4): "on a Γ_a = Γ'_a = ω(K*) pour tout a∈Φ et lorsque ω est discrète,
  l'échelonnage associé à φ^ω est de type A_r."
- (10.2.7): "On pose δ = ω'∘det. Proposition. — Soit 𝒮 l'ensemble des parties
  M de G telles que l'ensemble des ω(g_ij) pour g∈M et 1 ≤ i, j ≤ r+1, et
  l'ensemble des −δ(g) pour g∈M soient tous deux bornés inférieurement. …
  La bornologie définie par φ^ω est engendrée par 𝒮.H. Elle coïncide avec 𝒮
  si et seulement si G ⊂ Ker δ."

**Use.** Take `G = SL(X)`. It contains the `U_a`, so (10.2.2)–(10.2.3) apply.
If `ω` is discrete then `Γ_a = ω(K*)` is discrete, so `φ^ω` is discrete and
6.5 applies. `G'` contains the `U_a`, which generate `SL(X) = G`, so `G' = G`.
This gives clause 1, with `W` of type `Ã_{m-1}` by (10.2.4). Clause 2 is
(1.2.6)–(1.2.8). For clause 3: by (3.1.3)–(3.1.4) and (8.1.7) the Tits-system
bornology is the φ-bornology. `SL(X)` is the kernel of the Dieudonné
determinant, so `δ` vanishes on it, and (10.2.7) identifies the φ-bornology
with `𝒮`. On `SL(X)` the condition on `−δ` is empty.
