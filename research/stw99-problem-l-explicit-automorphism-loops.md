---
rg: 2
id: stw99-problem-l-explicit-automorphism-loops
kind: claim
title: Exhibit explicit generators of the fundamental group of Aut of the irrational rotation algebra (STW Problem L)
root: true
artifacts:
  - research/artifacts/stw99-actions-classification-cluster-2026-08-30.md
---

**Problem L of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Find
explicit loops generating `π_1(Aut(A_θ)) ≅ Z^6` (Gabe--Schafhauser in
progress, via the finite analogue of Dadarlat's
`π_k(Aut) ≅ KK^1(C_u A, S^k A)`), or of the matching UCT Kirchberg
algebra; more generally explicit `π_1(Aut(A))` generators for
UCT-Kirchberg or monotracial classifiable `A`.  STW: the rotation
action `T^2 ↷ A_θ` gives an injective `Z^2` (winding numbers through
`tr ∘ Bott ∘ ev`), suspected to be a direct summand; the other four
generators are unidentified.

**KIRCHBERG HALF ANSWERED (2026-09-04).**  Six explicit circle actions on
a UCT Kirchberg algebra with scaled graded K-theory `(Z^2,(1,0),Z^2)` are
now an established integral basis of its `pi_1(Aut)` --
`stw99-l-six-circle-actions-basis-of-pi1-aut`, with the four
retraction-kernel generators on `A_theta (x) O_infinity` in
`stw99-l-four-loop-basis-of-retraction-kernel`.  That is STW's own
"or of the matching UCT Kirchberg algebra" alternative, reached through
two fixed but nonconstructive classification isomorphisms.  It confirms
the conjecture recorded below in its shape -- four `Hom(K_1,K_0)` loops
plus two loops carrying the `K_0/Z[1] -> K_1` block -- but NOT its
mechanism: the four are edge-phase gauge loops on a three-vertex graph
model, not Rieffel-projection transport, and the last two are tensor-factor
actions rather than rotations.  **This root stays open**: it asks for loops
in `Aut(A_theta)` itself, and the weak homotopy equivalence supplies no
explicit preimages in the stably finite algebra.

## Attempts

* Bookkeeping candidate for the missing four: (i) INNER loops — the
  fibration `T → U(A_θ) → U/T` and `Ad : U/T → Aut` give a map from
  `π_1(U(A_θ))/⟨[1]⟩ ≅ K_0(A_θ)/Z[1] ≅ Z` into `π_1(Aut)`; (ii) the
  two `Z^2`-rotation loops; that accounts for at most 3 of 6, so at
  least three generators are neither inner nor rotational — they must
  move `K`-theory data invisibly (loops of approximately inner but
  not inner automorphisms, Thomsen's algebraic `K_1` territory), and
  the natural source is the `SL_2(Z)`-symmetry: paths conjugating the
  flip/Fourier automorphisms back to themselves trace loops whose
  Dadarlat classes live in the `Hom(K_1, K_0)`-part of
  `KK^1(C_uA, SA)` — exactly a rank-4 block
  (`K_1(A_θ) = Z^2 → K_0(A_θ) = Z^2`).  Conjecture recorded: the six
  generators are the two rotation loops plus four
  `Hom(K_1,K_0)`-loops realized by Rieffel-projection transport
  around the two circle directions; a groupoid model (STW's own
  suggested route, Mitscher--Spielberg style, easier on
  `A_θ ⊗ O_∞`) would make these visible.
