---
rg: 2
id: hughes-extension-lemma-and-fsp-universal-field-imports
kind: claim
title: Hughes-free embeddability passes to extensions, orderable groups have it, and when a Hughes-free division ring exists it is the universal field of every graph-of-rings splitting
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports existence for amenable, residually torsion-free nilpotent and free-by-cyclic groups, the graph-of-rings embedding, and the elementary amenable extension corollary; this imports Hughes' extension lemma for arbitrary locally indicable quotients, and FSP's Lemma 7.6 and Theorem 7.8, which identify the graph-of-rings field and the Lewin-Lewin field with the Hughes-free one once the latter exists.
  hughes-free-division-rings-pass-to-directed-unions: that is closure under directed unions; this is closure under extensions.
---

**ESTABLISHED (literature import)** by [[hughes-extension-lemma-and-fsp-universal-field-citation]].

`k` and `E` are arbitrary division rings, in any characteristic, and `*` denotes a crossed product.

**Definition (Hughes-free embeddable, HFE).** A locally indicable group `Γ` is *Hughes-free embeddable* if every
crossed product `E * Γ` over every division ring `E` has a Hughes-free division ring of fractions `D_{E*Γ}`.

The imported statements:

1. **Hughes' extension lemma.** Let `G` be locally indicable and `N ⊴ G` with `G/N` locally indicable. Let
   `K * G` be a crossed product. If `K * N` has a Hughes-free division ring `D` and `G/N` is HFE, then `K * G` has
   a Hughes-free division ring. More precisely, write `K*G = (K*N) * (G/N) ⊆ D * (G/N)`. Then the Hughes-free
   division ring of `D * (G/N)` is a Hughes-free division ring of `K * G`. In particular, an extension of an HFE
   group by an HFE group is HFE.
2. **Orderable groups.** Bi-orderable groups, and so torsion-free abelian groups, are HFE (Malcev–Neumann).
3. **The universal field is the Hughes-free field (FSP Lemma 7.6).** Let `G` be locally indicable, split as a
   graph of groups `G_Γ = (G_v, G_e; Γ)`. If `D_{k*G}` exists, then `U(DG_Γ) ≅ D_{k*G}` as `k*G`-rings. Here
   `DG_Γ` is the graph of division rings `(D_{k*G_v}, D_{k*G_e}; Γ)` and `U` is its universal division ring of
   fractions. In particular, FSP's Question 3.13 (q:HF) has a positive answer for `G_Γ` whenever `D_{k*G}`
   exists.
4. **Lewin–Lewin (FSP Theorem 7.8).** Let `G` be a torsion-free one-relator group and `k` a division ring such
   that `kG` embeds in a Hughes-free division ring `D_{kG}`. Then the Lewin–Lewin division ring of `kG` is
   `kG`-isomorphic to `D_{kG}`.
5. **Status of the one-relator case (FSP §7).** The Lewin–Lewin construction is known to be Hughes-free in
   characteristic 0 (Jaikin-Zapirain–López-Álvarez), and in every characteristic when `G` is virtually compact
   special. By Louder–Wilton and Linton this covers primitivity rank at least 3. FSP state that "only the
   primitivity rank 2 case remains in characteristic p > 0" (Question 7.13).
