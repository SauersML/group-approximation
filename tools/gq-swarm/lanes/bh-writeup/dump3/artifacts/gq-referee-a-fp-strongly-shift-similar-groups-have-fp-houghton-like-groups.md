# Referee report (gq-referee-a, proof-gap lens): finitely presented strongly shift-similar groups have finitely presented Houghton-like groups

**Reviewed** (coordinator request), read on origin/main:
- `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups` (6d130b349), with the proof inline;
- its two unreviewed elementary inputs, which I refereed as well because the node stands on them:
  - `finitary-mixing-of-fp-highly-transitive-groups-is-fp`;
  - `strongly-shift-similar-point-stabilizers-are-copies-of-the-group`.

**Verdict: PASS for all three.** There are three nits, all on the finitary-mixing input.
- For the citation lens:
  - Mallery–Zaremsky, Observation 5.1, Propositions 5.3 and 5.5, Lemma 3.19 and the wording of Question 5.13;
  - P. Hall's extension lemma.

## 1. The main node
- **Step 1.** The hypotheses (a)–(c) of the finitary-mixing node hold for the ray copies `G_k`:
  - (a) is the hypothesis;
  - (b) and (c) are items 1 and 2 of the stabilizer node, since `Stab ≅ G` is finitely generated. ✓
- **Step 2 (normality and the quotient).**
  - `H/FSym(X) ≅ Q_n(Ĝ)` is item 1 of the Houghton-like node, which I refereed as PASS (01bc75a40).
  - `B` maps onto `Germs(G)^n`, because every germ in `Germs(G)` is realized by some `g ∈ G`. This is the kernel of
    `(η_k)` on `Q_n`, because `ker η = Germs(G)` in `Ĝ = Germs(G) ⋊ ⟨s̄⟩`.
  - The image of `(η_k)` is `{Σc = 0}`, via `(s̄^(c_k))`.
  - The converse inclusion is correct: index-0 ray germs have the form `s̄^(a)ḡs̄^(−a) ∈ Germs(G)`.
  - So `B` is the full preimage, it is normal, and `H/B ≅ Z^(n−1)`. ✓
- **Step 3.** P. Hall's lemma applies. ✓
- **The calibrations.** They are consistent:
  - `H_1(G) = G`, because a single ray forces index 0;
  - `G = 1` and `G = FSym(N)` are excluded;
  - `H_n(H_k) ≅ H_(nk)`;
  - `H_2` is not finitely presented while `H_4` is;
  - free-shift envelopes are not finitely presented.

## 2. `strongly-shift-similar-point-stabilizers-are-copies-of-the-group`
- **Item 2.** On `Stab_G(j)`, `ψ_j` is conjugation by `s_j`, so it is an injective homomorphism.
- **Surjectivity.**
  - `fg ∈ Stab_G(j)`.
  - `ψ_j(fg) = φ·h`, with `φ = s_j^(−1) f|_(N∖{k}) s_k`. This is finitary, because `s_j` and `s_k` agree outside
    `[min(j,k), max(j,k)]`.
  - `φ^(−1) = ψ_j(s_jφ^(−1)s_j^(−1))`, and that argument is finitary and fixes `j`, so it lies in `G` by item 1. Hence
    `h ∈ ψ_j(Stab_G(j))`. ✓
- **Items 3 and 4.** They follow, by induction and by the representation of Proposition 5.5 respectively. ✓

## 3. `finitary-mixing-of-fp-highly-transitive-groups-is-fp`
- **The relations hold in `B`.**
  - (R2): elements fixing `x_1` and `y_j` commute with `(x_1 y_j)`.
  - (R3): `t_it_jt_i ↦ (y_i y_j)`.
  - (R4): these are true conjugation identities.
  - Finiteness: `G = ∏G_k` with each factor highly transitive, so orbits of ordered pairs of transpositions are fixed
    by the part and coincidence pattern of at most 4 points. ✓
- **Step 1.** `G → G̃ → G` is the identity, so `G̃ ≅ G`. ✓
- **Step 2.** Two choices `w, w'` differ by `w'w^(−1) ∈ Stab_G(x_1, y_j)`, which lies in `G̃` by Step 1. By (R2), that
  element commutes with `t_j`.
  - Across `X_1` and `X_j`, the orientation is forced, because `G` preserves each `X_k`.
  - For two parts `X_i` and `X_j` with `i, j ≥ 2`, see N1.
  - Equivariance holds: `g(w^(−1)t_jw)g^(−1) = (wg^(−1))^(−1)t_j(wg^(−1))`. ✓
- **Step 3.** The transposition relations `τ² = 1` and `τστ = τ(σ)`, over all pairs, present `FSym(X)` (N2).
  - Given equivariance, every such relation holds in `K̃`.
  - So `K̃ ≅ FSym(X)`. ✓
- **Step 4.**
  - `B̃ = G̃K̃`.
  - `π(w) ∈ G ∩ FSym(X) = ∏FSym(X_k)`, so `w` is a product of internal transpositions, which lie in `T̃ ⊆ K̃`.
  - So `wk ∈ K̃ ∩ ker π = 1`. ✓
- **Consistency with Houghton's `H_2`.** The calibration of the stabilizer node, with `H_2` not finitely presented,
  does not conflict with this input. `H_2`'s translation is not in `G_1 × G_2`, and `FSym(ray)` is not finitely
  presented. Here each `G_k` is finitely presented.

## Nits
- **N1 (finitary mixing, writing transpositions).**
  - For `a ∈ X_i` and `b ∈ X_j` with `i, j ≥ 2`, `(a b)` could be written either with `t_ij` or with `t_ji`, and these
    are different words.
  - Fix `i < j`. Then the braid relation `t_it_jt_i = t_jt_it_j` is an instance of (R4): take `τ = t_j` and
    `σ = t_i`, so that `τ(σ) = (y_i y_j)` is written `t_ij`.
  - Without the convention, the bijection `π : T̃ → {transpositions}` in Step 2 needs `t_ij = t_ji` first.
- **N2 (finitary mixing, Step 3).** Give the one-line reason that the transposition relations present `FSym(X)`.
  - Rack instances give the Coxeter relations for adjacent transpositions: `s_is_(i+1)s_i = (i, i+2) = s_(i+1)s_is_(i+1)`,
    and disjoint transpositions commute.
  - Every transposition is a conjugate of an `s_i` inside the presented group.
  - So the group is a quotient of each finite `Sym`, and then pass to the direct limit.
- **N3 (finitary mixing, (R3)).** Only the pairs `i < j` are needed, and `Stab_G(y_i,y_j)` is finitely generated by
  (c), as a product of point stabilizers and full factors. Say so.
