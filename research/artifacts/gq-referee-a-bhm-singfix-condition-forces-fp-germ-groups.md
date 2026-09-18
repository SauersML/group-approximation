# Referee report (gq-referee-a, proof-gap lens): the BHM SingFix condition forces finitely presented germ groups

**Reviewed:**
- `bhm-singfix-condition-forces-fp-germ-groups` and its `-proof` (lane gq-typeA-design, fcc524ea0), read on
  origin/main;
- on request, the lane remark under gate 1 of `steinberg-resolvent-shell-envelope-is-finitely-presented`.

**Verdict: PASS**, for both the node and the remark. There are two nits. The Belk–Hyde–Matucci definitions and the
quoted Theorem 2.1 hypothesis are for the citation lens.

## Checks (the three steps the author asked about)
- **Ontoness uses only condition (3), so `G` need not be full.**
  - *Case `p ∈ sing(g)`.* Condition (3) gives `h` with `sing(h) = {p}` that agrees with `g` near `p`. So
    `h(p) = g(p) = p`, `h ∈ S_p`, and `(h)_p = (g)_p`.
  - *Case `p ∉ sing(g)`.* This uses only the definition of a singular point: the germ of `g` at `p` is the germ of
    some `v ∈ V`. So `v(p) = p`, and `sing(v) = ∅` gives `v ∈ S_p` (N1).
  - No fullness hypothesis enters. ✓
- **The kernel is `K_p`.**
  - *Kernel ⊆ `K_p`.* If the germ is trivial, the germ is that of `1 ∈ V`, so `p ∉ sing(g)`. Hence `sing(g) = ∅`, and
    condition (2) gives `g ∈ V`, the identity near `p`.
  - *`K_p` ⊆ kernel.* `K_p ⊆ S_p`, and its elements have trivial germs at `p`. ✓
- **The identification `V[U] ≅ V_(2,r)`.**
  - A clopen `U` is a finite disjoint union of `r` cones.
  - `C − U` is open, so every point has a neighbourhood inside `U` or inside `C − U`.
  - Hence a locally-prefix-replacement homeomorphism of `U`, extended by the identity, is locally a prefix
    replacement everywhere. By compactness it has finitely many pieces, so it lies in `V`.
  - Conversely, restriction to `U` of an element of `V[U]` is such a homeomorphism.
  - So `V[U] ≅ V_(2,r)`, and `V_(2,r) ≅ V_(2,1) = V` (Higman, `r ≡ 1 mod 1`), which is simple. ✓
- **The directed union.**
  - `W ⊇ W'` gives `V[C−W] ⊆ V[C−W']`, and two proper clopen neighbourhoods of `p` contain a common cone. So the
    union is directed.
  - Every `v ∈ K_p` is the identity on some cone `W ∋ p`, so it preserves `C − W`.
  - For `W` proper and nonempty, `C − W` is a nonempty proper clopen set, so `V[C−W] ≅ V ≠ 1`.
  - A directed union of simple groups is simple (N2). ✓
- **Items 2 and 3.**
  - `⟨⟨k⟩⟩_(K_p) = K_p ⊆ ⟨⟨k⟩⟩_(S_p) ⊆ K_p`.
  - Adding one relator to a finite presentation of `S_p` presents `S_p/K_p ≅ (G)_p`. ✓
- **The Theorem 2.1 consequence.** `({p},{p})` has `|M'| = 1 ≤ n`, so type `F_1` and `F_2` of `S_p` give finite
  generation and finite presentation of `(G)_p`. The scope notes are correct: nothing lifts from `(G)_p` back to
  `S_p`. The `V_(d,r)` remark is marked as not proved.

## The optional lane remark (gate 1 of the shell-envelope node): correct
- `R_L` is a nonzero, finitely presented, simple unital ring.
  - `w = 0` is recursively enumerable.
  - If `w ≠ 0`, then `1 ∈ (w)`, which is recursively enumerable: search for `1 = Σ a_i w b_i` modulo the relations.
  - Since `1 ≠ 0`, `1 ∈ (w)` exactly when `w ≠ 0`. Running both searches decides `w = 0`. ✓
- A word in the elementary generators of `E_4(R_L)` is a matrix of ring words. It is trivial exactly when each
  entry equals `δ_ij`, which is decidable. ✓
- So the gate reduces, as stated, to deciding triviality of words of `St_4(R_L)` whose image in `E_4` is trivial,
  that is, words in `K_2(4, R_L)`. The remark may be marked reviewed.

## Nits
- **N1 (Step 2).** State the definition being used: `q ∉ sing(g)` means that `g` agrees near `q` with an element of
  `V`.
- **N2 (Step 4).** Add the one-line reason that a directed union of simple groups is simple. A nontrivial normal
  subgroup meets some `V[C−W]` nontrivially. It therefore contains every `V[C−W'] ⊇ V[C−W]`, hence contains the
  whole union.
