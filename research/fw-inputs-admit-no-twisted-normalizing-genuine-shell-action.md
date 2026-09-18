---
rg: 2
id: fw-inputs-admit-no-twisted-normalizing-genuine-shell-action
kind: claim
title: An infinite group with property FW has no faithful action on N that the shift conjugates into itself toward the singular point, so FW inputs never pass the window-zero shell gate in that direction
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that excludes window zero for regular enumerations of one-ended inputs; this excludes it for every genuine action with infinite supports, when the input has property FW.
  eventually-periodic-genuine-shell-actions-give-fp-envelopes: that shows genuine actions can pass window zero for the one-ended Z^2 via a rotation twist, and leaves twists of infinite order and by endomorphisms open; this closes them for FW inputs, for endomorphisms in the direction toward p and for automorphisms in both directions.
  normal-germ-extensions-of-v-have-only-finite-kazhdan-subgroups: that forbids Kazhdan germs normalizing the V-dilation; this forbids the V-dilation conjugating the Kazhdan germs into themselves.
  fw-inputs-admit-no-twisted-shell-normalization: that is the parallel result of lane gq-typeA-design at m = 1, landed independently, with a finite-support conclusion; this covers every power s^m, m > 0, for any map, and m < 0 for automorphisms.
  fw-shell-inputs-at-window-zero-are-highly-transitive: that treats the direction left open here (m < 0 with a non-surjective endomorphism) and shows it forces high transitivity on finitely many cofinite orbits, hence trivial centre; this closes the other direction and the automorphism case of this one.
  fw-window-zero-descending-sign-forces-trivial-core: that shows the same open direction forces a trivial endomorphism core, so co-Hopfian FW inputs fail it; this is the complementary ascending statement.
  fw-inputs-pass-window-zero-only-via-proper-self-embeddings: that is the index-formula form of the same picture (sign -1 only, through an injective endomorphism of infinite index); this is the direct straightening argument for m of any size.
---

**ESTABLISHED** by `fw-twisted-normalizing-shell-action-proof` (lane proof, elementary; not
independently reviewed; no novelty claimed).

**Statement.** Let `P` be an infinite group with property FW (every commensurated subset
of every `P`-set is transfixed), for instance a group with property (T). Let
`ρ : P -> Sym(N)` be an action in which every `g ≠ 1` moves infinitely many points, and
let `s(n) = n + 1`. For an integer `m ≠ 0` and a map `φ : P -> P`, consider

    (★)   s^-m ρ_g s^m = ρ_(φ(g))   near infinity (off a finite set), for every g in P.

1. For `m > 0`, (★) holds for **no** `φ`. Such a `φ` would be an injective endomorphism.
2. For `m < 0`, (★) holds for no **automorphism** `φ`.

**Shell reading.** In the genuine-action shell envelope `E_ρ` of
`genuine-action-shell-envelopes-generalize-the-regular-shell`, the ascending gate of
`shell-germ-fp-is-an-ascending-hnn-gate` with window `N = 0` and base `B = ρ(P)` is (★)
with `m = ±1`.
- Item 1 is the direction (G+) of `shell-a1-ascends-when-the-gate-points-toward-p`, in which
  the germ gate would also make `A_1` an ascending HNN extension. For FW inputs it is
  closed whatever the twist.
- Item 2 closes the other direction for automorphism twists.

This covers every infinite simple Kazhdan input, and hence every input that matters for
`boone-higman-conjecture` by `boone-higman-iff-simple-kazhdan-decidable-inputs`. It also
covers `St_N(R_L)` and the Deligne lattice. Main's `Z^2` example passes window zero only
because `Z^2` is not FW. A genuine-action shell for an FW input needs a window `N >= 1`, or
the direction away from `p` with a non-surjective endomorphism twist.

**Scope.** Item 2 for non-surjective endomorphisms is not proved here, since the index no
longer forces the orbits to be finite. It is treated by `fw-shell-inputs-at-window-zero-are-highly-transitive`
(high transitivity, so trivial centre and no finite normal subgroup) and
`fw-window-zero-descending-sign-forces-trivial-core` (trivial endomorphism core), both from lane
gq-typeA-design. Together they close it for FW inputs with nontrivial centre, such as the Deligne
lattice and `E_N(R_L)`, and for co-Hopfian FW inputs. Near actions that are not genuine actions are
not covered.
