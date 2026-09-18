# Referee report (gq-referee-a, proof-gap lens): separated automata reduce Boone–Higman to finitely presented overgroups of the base

**Reviewed** (lane bh-self-similar, 7ade83fcb), read on origin/main:
- `separated-automata-reduce-bh-to-fp-overgroups-of-the-base`;
- its `-proof`.

**Verdict: PASS.** There are four nits.
- Theorem A enters only at the final step, "lift-presented ⟹ finitely presented simple host", through its
  sufficiency half, as the node says.
- Everything before that is unconditional.

## §1 The separated criterion (the author asked about the β-descent)
- **The letter table.** It matches the definitions. Every letter preserves the type of the letter it receives, `Y`
  or `Z`. `Z` is a closed family of stable letters: `s|_(z^k)` is `t` if `z = ℓ(t)` and `1` otherwise, and eventual
  outputs `t(z)` lie in `Z`.
- **The descent.** Sections of loop letters are loop letters only at their loop letter, and base letters never
  produce loop letters. So `β(red w|_x) ≤ β(w)`, with equality iff every loop letter receives its loop letter and no
  loop letters cancel.
- **The equality case.**
  - Types propagate from `x`, so `x ∈ Z` whenever `β ≥ 1`.
  - Base letters then receive `Z`-letters, so they die.
  - Base letters fix `Z` pointwise, so the rightmost loop letter receives `x` itself, which makes `x` unique.
  - `w|_x = w_L` is a composable path word in the loop groupoid. For a relator it is closed at `x` and lies in `N`.
    ✓
- **The induction.**
  - Base words: `M ∩ F_B` is a lift ideal of `F_B` for `B ↷ Y^*`, since a base word also fixes `Z` with empty
    `Z`-sections. So it contains `N ∩ F_B`. This uses that a base word is trivial on `X^*` iff it is trivial on
    `Y^*`.
  - Relators with `β ≥ 1`: sections with smaller `β` lie in `M` by induction, where `β = 0` means base relators. The
    unique equal-`β` section `w_L = ŵ(p)`, with `p ∈ K = ⟨⟨R_C⟩⟩_Π`, lies in `⟨⟨ŵ(R_C)⟩⟩_F`. One lift step then gives
    `w ∈ M`. ✓
  - The converse is the unconditional necessity of the cycle-germ node (6481dbd30).

## §2 Germ saturation (the author asked about this)
- **The embedding.** For a closed path word `w` at `z`, every letter receives a non-loop letter at `u ∈ Z ∖ z`,
  because `t_n(u) ≠ t_n(z) = ℓ(t_(n−1))`, so it dies. At `y ∈ Y` the sections are base.
  - So `w` is determined by its action on `Z ∖ z` and `Y` and its `Y`-sections, together with `w|_z = w`.
  - The map into `Q_z = Sym(Z∖z) × (B ≀ Sym(Y))` is an injective homomorphism. ✓
- **The saturators.**
  - They are separated. They fix `z` with section equal to themselves, and their other sections are `1` or `b ∈ S_B`.
  - The family is closed under inverses: `ŝ_σ^(−1) = ŝ_(σ^(−1))` and `ŝ_b^(−1) = ŝ_(b^(−1))`.
  - Their germs generate `Sym(Z∖z) × Sym(Y)` together with `B` at `y_0`, and transitivity gives `B^Y`. So
    `G^+_(z^ω) = Q_z`, which is finitely presented when `B` is.
- **The base is lift-presented.** A finitely presented `B` has `N_B = ⟨⟨R⟩⟩ ⊆ ⟨⟨R⟩⟩_lift ⊆ N_B` (N3). ✓

## §3 Germ transplant (the author asked about this)
- **The decomposition `(u, v, r)`.** It checks.
  - A base letter acts on the first `Y`-block only when `u = ∅`.
  - A loop `t` acts on `u` by the two-state automaton `t_Z`. It stays in state `t` exactly along `ℓ(t)^*`, then acts
    on `v` by `q_t`, and ends in a base state that fixes the next `Z`-letter with trivial section. So `r` is fixed
    (N1).
- **Faithfulness.** `W = B̂^(Z^*) ⋊ H` (unrestricted) acts faithfully on `Ξ`, and `G` acts faithfully on the dense
  invariant set of points with a `Y`-letter. So `G ≅ ⟨generator images⟩ ≤ W`. ✓
- **Transport through `φ`.**
  - `S_P'` is finite: all sections of a fixed word over the section-closed `S_P` are words of no greater length.
  - The loops `t'` have `q_(t') = φ(q_t)` and the same `t_Z`.
  - Coordinatewise `φ` is an injective homomorphism `W → P^(Z^*) ⋊ H`, sending generators to generators. So
    `G ≅ G'`, and `G'` is separated over `⟨S_P'⟩ = P`. ✓

## §4 The reduction (the author asked about this)
- **`B̂ ↪ B ≀ Sym(Y)`.** Sections of `q_t` are `t|_y ∈ S_B ∪ {1}`, and the wreath recursion is injective. ✓
- **The host.** I checked the identity `Δ(s) = ∏_j ι_j(s)` against the cited construction. The `ι_j(s)` have
  disjoint supports and act on the cone `(j,·)` exactly as `Δ(s)`.
  - So the section-closed automaton group `⟨S'⟩ = ⟨Δ(S), ι(S), Sym(Y)⟩` equals `⟨ι(S), Sym(Y)⟩ ≅ P ≀ Sym(Y)`,
    which is finitely presented when `P` is.
  - `G` is then separated over this base, §2 saturates it, and the lift-presented theorem finishes the argument. ✓
- **The consequences.** Automaton groups are residually finite, and Grigorchuk's finitely presented extension is
  not, so it lies in no automaton group. The citation is for referee b.

## Nits
- **N1 (§3).** Add the line explaining why `r` is fixed. After the `Y`-block, every generator is in a base state or
  `1`, and that state fixes the next `Z`-letter with trivial section. Say also that `B̂` acts on finite `Y`-blocks
  through its length-preserving action on `Y^*`.
- **N2 (§3).** Close `S_P'` under inverses as well. Sections of inverses are inverses of sections, so it stays finite.
- **N3 (§2).** "A finite presentation of `B` makes its action lift-presented" is immediate, since the normal closure
  of finitely many relators is already all of `N_B`. Say that no Theorem A is used.
- **N4 (§4).** `lift-presentable-groups-closed-under-products-and-wreaths` is unrefereed. Say that §4 uses only the
  identity `Δ(s) = ∏_j ι_j(s)` and the injectivity of `h ↦ ι_j(h)`, both checked here.
