# Adversarial check: `ascending-hnn-of-free-groups-satisfy-boone-higman` (bh-refute, 2026-09-18)

An independent red-team verification of bh-free-05's ESTABLISHED lane proof
(`ascending-hnn-of-free-groups-bh-proof`, artifact `gq-bh-bh-free-05-ascending-hnn.md`).
Verdict: **PASS**. No gap found. The one import, BLIW `thm:free-groups`, is taken as quoted verbatim there
(TeX with SHA-256), and its scope matches.

## What was checked

1. **Hall step.**
   - Completing each letter's partial injection on the vertex set of the folded graph of
     `K = φ(F)` gives a connected `|V|`-sheeted cover. Domain and codomain defects have equal size,
     so the completion exists.
   - The maximal tree of `Γ_K` spans the cover, so the edges outside it give a free basis of `C_2`
     that contains one of `K`. Hence `C_2 = K * L`.
2. **Equal index.** `C_1 = ker(Y → Z/d; a_i ↦ 0, b ↦ 1)` has index `d`. Its covering graph (a_i-loops at
   every vertex, a b-cycle), with the b-path as maximal tree, gives `C_1 = F * R` with `F` the loops at 0.
   Checked.
3. **Ranks.**
   - Schreier gives `rank C_i = d(rank Y − 1) + 1 = dn + 1` for both.
   - `rank φ(F) = rank F = n`, since `φ` is injective, so `φ(F) ≅ F_n`.
   - Grushko additivity gives `rank R = rank L = dn + 1 − n`.
   - So `Φ = φ * α` is an isomorphism `C_1 → C_2` extending `φ`.
4. **Class membership.** In BLIW's definition (§11) of `BS_G`, with `G = F_2`:
   - the vertex group `Y ≅ F_{n+1}` and edge group `C_1 ≅ F_{dn+1}` are free of rank `>= 2`, so they are
     commensurable with `F_2`;
   - both edge inclusions have index `d`;
   - it is a finite (one-edge) graph of groups.

   `thm:free-groups` quantifies over *every* group in `BS_{F_k}`, `k >= 2`, with no faithfulness
   hypothesis on the member itself. The faithful Burger–Mozes member is internal to their proof. So the
   theorem applies to `H = Y*_Φ` as stated.
5. **Injectivity.**
   - `θ` is well defined, since `s g s^{-1} = Φ(g) = φ(g)`.
   - It is injective on the ascending union `B = ⋃ t^{-k} F t^k`, because it is injective on `F ≤ Y ≤ H`
     and hence on each conjugate.
   - `ker θ ⊆ ker(ε ∘ θ) = B`, since the height maps are compatible. So `ker θ = 1`.
6. **Degenerate cases.** `n = 0` is trivial. `n = 1` gives `BS(1,m)`, consistent with BLIW. `φ` must be
   injective for `F*_φ` to be an ascending HNN extension; this is part of the hypothesis.

## Attacks tried (all failed)

- **Non-injectivity through the base.** Excluded by the height-map argument; the kernel of an ascending
  HNN extension map is detected on the base.
- **The rank bookkeeping when `φ(F)` has infinite index in `F`.** This is harmless: Hall's theorem only
  needs `φ(F)` finitely generated, and the auxiliary letter `b` equalises the indices.
- **Hidden faithfulness hypotheses in BLIW (cf. their (H4)-type conditions in other statements).** Not
  present in `thm:free-groups` as quoted. The faithful member is produced inside their proof.

## Priority

An arXiv API search on 2026-09-18 over all abstracts mentioning Boone–Higman (16 entries, newest
2609.01868) found none mentioning ascending HNN extensions, mapping tori of non-surjective endomorphisms,
or generalised Baumslag–Solitar groups beyond BLIW's own free-by-cyclic and BS cases. That is consistent
with the node's "no priority claimed; bounded search".
