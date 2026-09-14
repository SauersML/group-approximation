# Lane hl-one-cell-l2: the first L²-Betti number of one-cell complement groups (2026-09-14)

Target: `one-cell-complement-groups-have-vanishing-first-l2-betti` (OPEN).

## 1. Sources read at source on MSI (2026-09-14)

- **Lück, *L²-Invariants from the Algebraic Point of View*, arXiv:math/0310489**, TeX `ltwoalg.tex`,
  kept in `/scratch.global/sauer354/hl-one-cell-l2/`. Pinned passages:
  - l.1127–1178: definitions of `b_p^(2)(X; N(G))` and `b_p^(2)(G)`;
  - l.1292: singular = cellular lemma;
  - l.1317–1345: homology invariance;
  - l.2383–2415: mapping tori, "taken from [Lück's book, Theorem 6.63]";
  - l.3467–3477: Theorem 6.4, items (vi) and (vii).

  Items 1–4 of `lueck-mapping-tori-and-homology-invariance-citation` quote them.
- **Osin--Thom, arXiv:1108.2411v2**, TeX `norm_3.tex`, in `…/hl-one-cell-l2/ot/`.
  - l.97–99: Conjecture `conj1`, the torsion-free normal-rank inequality.
  - l.103–108: Theorem `main2`, the limits of left-orderable amenable groups.
  - l.462: Conjecture `conj2` for torsion-free groups or `p`-groups: "$\beta_1^{(2)}(G/ \! \ll g_1,\dots,g_n \rr) \geq \beta_1^{(2)}(G)-n.$"
  - l.470, verbatim: "An important case is given by $X \subset X \cup_f D^2$ for some $f \colon S^1
    \to X$, with $X \cup_f D^2$ two-dimensional and contractible. While it is easy to see that
    $\nrk(\pi_1(X))=1$, Berrick and Hillman \cite{berhil} showed that $\beta^{(2)}_1(\pi_1(X))=0$
    implies that $X$ is aspherical."
  - l.500: "J. Berrick, J. Hillman, The Whitehead conjecture and $\ell^2$-Betti numbers, Guido's Book
    of Conjectures,".

  So the implication in `whitehead-one-cell-counterexamples-have-positive-first-l2-betti` is
  attributed there to Berrick--Hillman. That node currently says "likely in Hillman … (not
  checked)". This lane did not edit it; its owner may add the attribution.

## 2. Answers to the decisive steps

1. **The Osin--Thom question.**
   - The open question is Conjecture `conj1` restricted to finitely generated torsion-free groups.
     The countable form is refuted (`l2-normal-rank-bound-fails-for-torsion-free-groups`).
   - Proved cases in the source: finitely generated limits of left-orderable amenable groups, with
     the stronger bound `β₁^(2) ≤ β₁ − 1`.
   - No residually-`p` or locally indicable case is stated in the source.
   - The authors state that `main2` has no nontrivial application to Whitehead (l.472).
   - Landed as `lo-amenable-limit-one-cell-complements-are-aspherical`.
2. **(a) Cyclic towers.** The subgroups `φ⁻¹(nZ)` intersect in `[G, G]`, not in `1`, so Lück
   approximation along them does not compute `b₁^(2)(G)`.
   - Their Betti numbers are bounded. Use the sequence of `K_∞ → K_n` with deck group `nZ`:
     `H₁(K_∞) --(tⁿ−1)--> H₁(K_∞) → H₁(K_n) → H₀(K_∞) --0--> H₀(K_∞)`.
   - It gives `dim H₁(K_n; Q) ≤ dim H₁(K_∞; Q) + 1 < ∞`, by
     `one-cell-complement-cyclic-cover-homology-is-finite`.
   - **(b) The Alexander module.** It is always torsion, and `H₂(K_∞) = 0` (same node). The
     hypothesis "the cyclic cover has finitely generated rational `H₁`" is automatic and cannot be
     the missing input. A χ = 0, `H₁ = Z`, `H₂ = 0` complex `S¹ ∨ P`, with `P` the complex of
     `⟨x, y | x² = y³ = (xy)⁵⟩`, has the same cyclic-cover rational homology and `b₁^(2) > 0`.
3. **Strongest theorem landed.**
   - `ascending-hnn-one-cell-complements-have-vanishing-l2-b1` covers every one-cell complement
     whose group is `H *_σ` with `H` finitely generated. That includes all with finitely generated
     commutator subgroup, and all without non-abelian free subgroups (Bieri--Strebel, recalled).
   - The route's steps 1–5 show `b₁^(2)(H *_σ) = 0` for every ascending HNN extension of a finitely
     generated group.
   - No novelty is claimed.
   - **The exact gap** is `non-ascending-one-cell-complements-have-vanishing-l2-b1`.

## 3. Checks

- `BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩` is a one-cell complement: adding `t` gives a simply connected
  complex with χ = 1 and `H₂ = 0`. Its kernel is `Z[1/2]`.
  - `t − 1` is invertible on `Z[1/2] ⊗ F_p` for odd `p`, and on `⊗ Q`; `⊗ F₂ = 0`.
  - `H = Z` and `σ = ×2` are consistent with the ascending claim.
- `S¹ ∨ P` has `π₂ ≠ 0`: the universal cover of `P` has χ = 120 and is simply connected. The complex
  retracts to `P`, so the landed criterion forces `b₁^(2) > 0`. The group order 120 is recalled.
- Mapping-torus words: the 2-cell `x_j × (0, 1)` has boundary `x_j τ w_j⁻¹ τ⁻¹`, so
  `τ⁻¹ x_j τ = w_j`. `φ(τ) = t⁻¹` sends this to `t h_j t⁻¹ = σ(h_j)`.

## 4. Not done

- The LOT literature (Howie, Rosebrock, Harlander--Rosebrock) was not read at source in this lane.
  So whether the ascending case for LOT groups is already recorded there is unchecked.
- The Bieri--Strebel no-free-subgroup theorem, BNS symmetry for 3-manifolds, and the Lott--Lück
  vanishing for knot exteriors are recalled only.
