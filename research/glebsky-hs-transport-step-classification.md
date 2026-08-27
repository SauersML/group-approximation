---
rg: 2
id: glebsky-hs-transport-step-classification
kind: claim
title: Which steps of Glebsky's permanence proof survive normalized-HS transport
invalidates: [glebsky-verbatim-hs-transport]
distinct_from:
  glebsky-weak-soficity-is-metric-free: that records that the permanence proof constructs no metric; this classifies each of its six steps by whether it transports to (U(n), normalized HS), and proves that one of them cannot
  glebsky-manufactured-invariant-length: that extracts the length Lemma 3 of the 2017 paper manufactures; this is about the 2019/2023 permanence proof that consumes it, and about what breaks when the class is not Fin
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks whether a Hilbert embeddable witness exists; this says that even granting one, the equational architecture that produces Glebsky's witnesses cannot be rerun over unitary groups
artifacts:
  - notes/TRUE_GLEBSKY_HS_TRANSPORT_AUDIT.md
---

Step classification of Glebsky, arXiv:1910.08631 (published as Rev. Mat.
Iberoam. 39 (2023) 1097–1104), read in full from the PDF 2026-08-14.
Type (a) = works for any approximation class closed under subgroups and
residual limits; type (b) = needs the class to be `Fin`.

1. **(a) Kaluzhnin–Krasner.** `K` RF-by-RF `⟹ K ≤ H ≀ G`, the **unrestricted**
   wreath product `H^G ⋊ G`. Survives: hyperlinearity passes to subgroups.
   Worth noting on its own — for `H` finite and `G` infinite this group is
   *amenable-by-sofic*, which Elek–Szabó's sofic-by-amenable theorem does not
   cover, and its soficity is the open question Glebsky's §7 leaves open.
2. **(a) Residual reduction.** `H` RF `⟹ H ≀ G` residually `{H_i ≀ G}` with
   `H_i` finite; residually-𝒞 `⟹` 𝒞. Survives: approximability is a local
   property, so residually hyperlinear implies hyperlinear.
3. **(b) The characterization** `K` weakly sofic `⟺` every `w̄ ∈ Sys(Fin)`
   solvable over `K`. This is Corollary 19 of arXiv:1506.06940, whose stated
   hypothesis is `K ⊆ Fin`, and whose engine is that paper's Lemma 3.
4. **(b) The universal solution (Lemma 4).** `X_N ≠ ∅` because `D_N ⋊ G_N` is
   a **finite** group in which `w̄ ∈ Sys(Fin)` is solvable; then `X = lim_← X_N`
   is nonempty by compactness of an inverse limit of nonempty **finite** sets.
5. **(a) Locality (Lemma 5).** `ψ(x) = ψ̃(x_γ)` whenever `x·Suf(p)(ᾱ) ⊆ T_γ`.
   Purely combinatorial; survives verbatim.
6. **(a) Tychonov limit (Lemma 6).** Survives verbatim; the only compactness
   used is that `H^Γ` is compact for `H` finite.

**Step 4 provably does not transport.** For a hyperlinear analogue the system
class is `Sys(𝒰)` = systems solvable in every `U(n)`, and the step would need
`w̄ ∈ Sys(𝒰) ⟹ w̄` solvable in the finite group `D_N ⋊ G_N`. Take `w̄` to be
`x²a⁻¹`: every unitary has a square root, so `w̄ ∈ Sys(𝒰)`, but `w̄` fails in
`ℤ/2` with `a` the nontrivial element, and `ℤ/2` is a quotient of `D_N ⋊ G_N`
when the lamp is `ℤ/2`. More generally Gerstenhaber–Rothaus puts every system
with nonsingular exponent matrix in `Sys(𝒰)`, and such systems routinely fail
in finite groups. The conclusion is about the *method*, not about `W`: the
system `x²=a` is solvable over every group by Higman–Neumann–Neumann.

This is the same failure, at the same step, that Glebsky records for the sofic
case in his §7: *"The problem is that solvability in permutation groups is not
enough to prove, say, the existence of universal solutions."* Soficity and
hyperlinearity are blocked identically here, so nothing about the difficulty is
special to unitaries.

**Calibration: the neighbouring metric analogue is false.** Glebsky's own
reference [6] is De Chiffre–Glebsky–Lubotzky–Thom arXiv:1711.10238, which
exhibits a **residually-finite-by-finite** group that is not approximable by
`U(n)` in the **Frobenius** (unnormalized Hilbert–Schmidt) norm. They state
verbatim: *"Our techniques do not apply directly to the context of (iii) [the
normalized Hilbert–Schmidt norm], so we cannot say anything conclusive about
Connes' Embedding Problem."* So Theorem 1 is false for the nearest neighbouring
metric class and open for the normalized one; it is not metric-robust, and no
argument may treat "some invariant metric" and "the HS metric" as interchangeable.
