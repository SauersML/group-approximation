---
rg: 2
id: thickenable-z-pairs-move-class-proof
kind: route
title: Proof that every orientably thickenable Z-pair in F_3 is (P1)/(P2)-equivalent to a basis pair, by uniqueness of genus-3 Heegaard splittings of the solid torus and the disc-slide lemma for compression bodies
target: thickenable-z-pairs-lie-in-the-move-class-of-a-basis-pair
requires:
  - one-stabilization-ac-trivial-from-thickenable-z-pair
  - one-stabilization-ac-trivial-from-primitive-relator
---

All manifolds are PL and orientable. F = F(a, b, c). Moves (P1), (P2) are as in the target.

**Cited results.**
- (HS) Every Heegaard splitting of a handlebody is standard: it is a stabilization of the
  minimal-genus splitting, and two splittings of the same genus are isotopic.
  Scharlemann–Thompson, "Heegaard splittings of (surface) × I are standard",
  Math. Ann. 295 (1993) 549–564. See also Scharlemann, "Heegaard splittings of compact
  3-manifolds", Handbook of Geometric Topology (2002), §3.
- Compression bodies are irreducible, and ∂₋ of a compression body is incompressible.

## Step 1: the splitting of a thickenable pair

Let r = (r_1, r_2) be a thickenable Z-pair, and let N be a regular neighbourhood of its complex.
By Steps 1–3 of `one-stabilization-thickenable-z-pair-criterion-proof`:
- N = H ∪ h_1 ∪ h_2, with H a genus-3 handlebody (one 0-handle, 1-handles for a, b, c);
- h_i is a 2-handle attached along c_i ⊂ ∂H, and c_i, read in the cocores of the 1-handles,
  is a conjugate of r_i^{±1} (possibly unreduced);
- N ≅ S¹ × D², and ∂N is a torus T.

Let C = (∂H × I) ∪ h_1 ∪ h_2, attached on ∂H × {1}. Then N = H ∪_{∂H} C.
- ∂C = ∂H ⊔ T, since ∂N = T is connected.
- So C is a compression body with ∂₊C = ∂H of genus 3 and ∂₋C = T.
- The cores Δ_r = {D_1, D_2} of h_1, h_2 cut C into T × I. Call such a pair of disjoint
  discs a *complete system*.

So (H, C) is a genus-3 Heegaard splitting of the solid torus N.

The basis pair (b, c) gives the model N_0 = H_0 ∪ C_0. Its 2-handles run once over the
b- and c-handles, and its complete system is Δ_0.

## Step 2: an automorphism and a complete system

Choose a homeomorphism g: N → N_0. Then (g(H), g(C)) is a genus-3 Heegaard splitting
of N_0. By (HS) it is isotopic to (H_0, C_0). Composing g with the isotopy gives a
homeomorphism f: N → N_0 with f(H) = H_0 and f(C) = C_0.

**The automorphism.** f|_H: H → H_0 induces an isomorphism π_1(H) → π_1(H_0). Both groups
are identified with F by the 1-handle cocores, so this is an automorphism φ of F, up to
an inner automorphism. The curve f(c_i) ⊂ ∂H_0, read in the cocores of H_0, is a conjugate
of φ(r_i)^{±1}. So r ~ (w_1, w_2) by (P2) and then (P1) conjugation and inversion, where
w_i is the word read by f(c_i).

**The complete system.** f(Δ_r) is a complete system of C_0 with boundary curves f(c_i).

## Step 3: disc-slide lemma

**Lemma.** Any two complete systems Δ, Δ′ of a compression body C with ∂₋C = T a torus
and ∂₊C of genus 3 are related by isotopy and disc slides.

Here a slide of D ∈ Δ over the other disc D_* ∈ Δ, along an arc β ⊂ ∂₊C from ∂D to ∂D_*,
replaces D by the band sum of D and a parallel copy of D_* along β.

Two facts are used throughout:
- (F1) If a compression body has ∂₋ = T and ∂₊ of genus 2, then cutting it along any
  non-separating disc gives a compression body with ∂₋ = T and ∂₊ of genus 1. That is
  T × I.
- (F2) A slide preserves completeness, since it changes C cut along Δ by a homeomorphism.

**Proof.** Isotope Δ′ to be transverse to Δ with |Δ ∩ Δ′| minimal. By irreducibility,
Δ ∩ Δ′ has no closed curves. Induct on the number of arcs.

*No arcs.* Let W = C cut along Δ ≅ T × I, with four spots D_1^±, D_2^± on T × {1}.
- Take E ∈ Δ′. Then ∂E ⊂ T × {1} minus the spots.
- T × {1} is incompressible in T × I, so ∂E bounds a disc Σ ⊂ T × {1}. By irreducibility,
  E is parallel to Σ in W.
- E is non-separating in C. If Σ held both spots or neither spot of each D_i, then ∂E
  would separate. So Σ contains exactly one spot of some D_i.
- A disc parallel to Σ is obtained from D_i by one slide over the other disc D_j for each
  spot of D_j inside Σ. So E is D_i after at most two slides over D_j.
- By (F2), Δ_1 = {E, D_j} is complete.

Let E′ be the other disc of Δ′. It is disjoint from Δ_1, so ∂E′ bounds a disc Σ′ on the top
of C cut along Δ_1.
- Suppose Σ′ held both spots or neither spot of D_j. Then Σ′ holds exactly one spot of E.
- In that case E and E′ cobound, with an annulus of ∂₊C, a region of C meeting Δ_1 only
  in E and in any D_j-spots inside Σ′. That region is a component of C cut along Δ′,
  which contradicts completeness.
- So Σ′ holds exactly one spot of D_j, and E′ is D_j after at most two slides over E.
- Hence Δ′ is reached from Δ by at most four slides.

*Some arcs.* Take an arc of Δ ∩ Δ′ outermost on a disc E ∈ Δ′. It cuts off a subdisc E_0
with E_0 ∩ Δ = α, an arc in some D ∈ Δ.
- Let D_* be the other disc of Δ, and let W_1 = C cut along D_*. W_1 has ∂₋ = T and ∂₊ of
  genus 2.
- α cuts D into D′ and D″. Put G_1 = D′ ∪ E_0 and G_2 = D″ ∪ E_0, pushed off D.
- D is a band sum of G_1 and G_2 in W_1, so [D] = [G_1] + [G_2] in H_2(W_1, ∂W_1; Z/2).
- D is non-separating in W_1, so some G_k is non-separating in W_1.
- By (F1), Δ_G = {D_*, G_k} is a complete system of C.
- Δ_G is disjoint from D, so by the no-arc case it is slide-equivalent to Δ.
- |Δ_G ∩ Δ′| < |Δ ∩ Δ′|, so by induction Δ_G is slide-equivalent to Δ′. ∎

## Step 4: slides are (P1) moves

Let Δ = {D_1, D_2} with boundary curves reading (u_1, u_2), and slide D_1 over D_2 along β.
The new boundary curve is the band sum of ∂D_1 with a parallel copy of ∂D_2 along β. Base
the reading at ∂D_1 ∩ β, and let γ be the word read along β. The new curve reads
u_1 · γ u_2^{±1} γ^{-1}, up to conjugation and free reduction. That is a (P1) move.

An isotopy of the boundary curves in ∂H_0 changes the words only by conjugation and by
inserting or deleting cancelling pairs. Those are (P1) moves.

## Step 5: conclusion

By Step 3, f(Δ_r) is carried to Δ_0 by slides and isotopy. By Step 4, (w_1, w_2) is carried
to (b, c) by (P1) moves. With Step 2, r reaches (b, c) by moves (P1), (P2). ∎

## Corollary B1

For a Z-pair s, the following are equivalent:
- s reaches a thickenable pair;
- s reaches (b, c);
- s reaches a pair with a primitive entry.

(1)⇒(2) is Theorem B and (2)⇒(3) is trivial.

(3)⇒(1): after (P2), suppose the primitive entry is a. Then (P1) moves delete a from the
other entry, leaving r_2′ ∈ F(b, c) with ⟨b, c | r_2′⟩ ≅ Z. A one-relator group on two
generators is Z only when its relator is primitive, so a further (P2) move gives (a, b).
That pair is thickenable, since its complex is a wedge of a circle and two discs.
