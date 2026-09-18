---
rg: 2
id: strongly-shift-similar-type-f-m-passes-to-houghton-like-groups
kind: claim
title: If a strongly shift-similar group G is of type F_m then every Houghton-like group H_n(G) is of type F_m, for all n >= 1 (Mallery-Zaremsky Question 5.13 for strongly shift-similar G)
requires:
  - finitary-mixing-preserves-type-f-m
  - fp-strongly-shift-similar-groups-have-fp-houghton-like-groups
  - houghton-like-groups-are-strongly-shift-similar
distinct_from:
  fp-strongly-shift-similar-groups-have-fp-houghton-like-groups: that is the case m = 2 (finite presentation); this is every m, including m = infinity, with the same normal subgroup and a cube-complex proof of its finiteness.
  houghton-like-envelopes-lift-finite-presentation-from-germs: that (refuted) assumed only a finitely presented germ group; this assumes G itself of type F_m.
  fp-strongly-shift-similar-admits-type-a-action: that is Zaremsky's type (A) theorem; this is about finiteness properties of the Houghton-like groups built from G.
---

**ESTABLISHED** (lane proof, below; not independently reviewed; no priority claimed). The imports were read at
source (see `finitary-mixing-preserves-type-f-m` and step 3).

**Priority search** (bounded, 2026-09-18).
- *Calibration.* The planted positive is arXiv:2405.18354 (Zaremsky, *Finite presentability of twisted
  Brin–Thompson groups*), which cites the source.
- *Semantic Scholar.* Citations of arXiv:2202.00822 and of DOI 10.4171/JCA/106: 2 papers, 2405.18354 (planted
  positive, found) and 2309.16613 (Tarocchi, conjugacy in rearrangement groups). The first uses shift-similar
  groups for type (A) actions. The second is about conjugacy. Neither addresses Question 5.13.
- *OpenAlex.* Reports 0 citations, so it is blind (it misses the planted positive) and is not relied on.
- *arXiv API metadata searches.* "Houghton-like" gives only the source. "shift-similar" gives only the source
  among mathematics papers.
- *Web searches.* Three queries found no later work on finiteness properties of `H_n(G)`. They did find the
  related but distinct Cox–Kropholler–Martino arXiv:2508.07816, on subgroups of `H_n` mapping onto `Z^(n-1)`,
  which does not concern `H_n(G)`.
- *Blind spots.* Full-text citation indexes (Google Scholar, zbMATH citations) were not reachable (zbMATH 403 or
  404). Papers that do not cite the source are not covered.

**Statement.** Let `G <= Sym(N)` be strongly shift-similar (Mallery--Zaremsky arXiv:2202.00822, Definition 3.17)
and of type `F_m`, with `1 <= m <= infinity`. Then `H_n(G)` is of type `F_m` for every `n >= 1`.

**Relation to Mallery--Zaremsky Question 5.13.** The question reads: "If a shift-similar group `G` is finitely
presented and `n >= 3`, then is `H_n(G)` finitely presented? If `G` is of type `F_m` and `n >= m+1`, then is
`H_n(G)` of type `F_m`? If `G` is strongly shift-similar, then do these results hold for all `n`?"
- The third sentence is answered **yes**, for both finiteness properties.
- The first two sentences are answered yes for strongly shift-similar `G`, and also for finite `G`:
  - finite shift-similar groups are the `S_k` (source Lemma 3.6);
  - then `H_n(G) = H_n` (Observation 5.2), which is of type `F_(n-1)` (Brown, recalled in the source);
  - so `n >= m+1` gives `F_m`, and `n >= 3` gives finite presentation.
  - Here `n >= m+1` cannot be dropped: `G = 1` is of type `F_infinity`, while `H_n` is not of type `F_n`.
- **The remaining case** is infinite, finitely generated, not strongly shift-similar `G`. Such `G` exist without
  finite generation (`infinite-shift-similar-groups-need-not-be-strongly-shift-similar`, answering the source's
  Question 3.18 as printed). No finitely generated one is known
  (`fg-infinite-shift-similar-groups-are-strongly-shift-similar`, OPEN). If that node is true, Question 5.13
  is answered positively in full.

**Proof.** Write `X = [n] x N`, `H = H_n(G)`, and `G_k` for the copy of `G` on ray `k` (Observation 5.1).
1. `B = (G_1 x ... x G_n) · FSym(X)` is of type `F_m`. By `finitary-mixing-preserves-type-f-m` item 3, each
   `(ray k, G_k) ∈ 𝔐_m`. Then apply item 2.
2. `B` is normal in `H` with `H/B ≅ Z^(n-1)`. This is step 2 of `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`,
   which reads it off from the germ isomorphism `H/FSym(X) ≅ Q_n(Ĝ)`.
3. `Z^(n-1)` is of type `F_infinity`. An extension of a group of type `F_m` by a group of type `F_m` is of type
   `F_m`. Source: Geoghegan, *Topological Methods in Group Theory*, Section 7.2, Exercise 1, read at source (PDF
   hash in `finitary-mixing-preserves-type-f-m`): "Let `N ↣ G ↠ Q` be a short exact sequence of groups. Prove that
   if `N` has type `F_n` and `Q` has type `F_n` then `G` has type `F_n`. Hint: see Theorem 7.1.10." The text after
   Theorem 7.2.21 also asserts it. (Correction: an earlier version cited "Theorem 7.2.21" from memory. That theorem
   is the quotient statement, "If `G` has type `F_n` and `N` has type `F_(n−1)` then `Q` has type `F_n`".) The
   exercise is a standard consequence of the Borel construction (Theorem 7.1.10). ∎

**Corollaries.**
- **Bootstrapping from one level.** Let `G` be any shift-similar group with `H_k(G)` of type `F_m` for some `k`.
  Then `H_(jk)(G)` is of type `F_m` for every `j >= 1`. Proof: `H_k(G)` has a strongly shift-similar representation
  and `H_j(H_k(G)) ≅ H_(jk)(G)` (Proposition 5.5).
- **Zigzag envelope.** `E_nu(Z)` with the zigzag `nu` is strongly shift-similar of type `F_3`
  (`zigzag-cyclic-shift-envelope-is-finitely-presented`, whose route `zigzag-cyclic-shift-four-ray-proof` is not
  rechecked here). So every `H_n(E_nu(Z))` is of type `F_3`.
- **Stabilizers.** Finite-set stabilizers of `B` are of type `F_m` (item 1 of the mixing node, `B ∈ 𝔐_m`).

**Calibrations.**
- `G = H_k` (strongly shift-similar representation, type `F_(k-1)`): the theorem says `H_n(H_k) ≅ H_(nk)` is of type
  `F_(k-1)`. The truth is `F_(nk-1)`, so the bound is consistent but not sharp. Finiteness can strictly improve.
- `G = H_2` (type `F_1`, not `F_2`): `H_2(H_2) ≅ H_4` is finitely presented. So the converse fails.
- `G = FSym(N)` is strongly shift-similar but not finitely generated. It is excluded, consistent with `H_n` not being
  of type `F_n`.

**For Boone--Higman.** Nothing new for inputs whose envelope `G` is already finitely presented. The open room on the
Houghton-like route is still an enumeration with `E_nu(P)` not finitely presented but some `H_n(E_nu(P))` finitely
presented. See `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`.
