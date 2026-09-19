---
rg: 2
id: m11-balanced-loop-host-has-exact-finite-l-presentation
kind: claim
title: The balanced-loop host R° = <M_11, b, C> has an exact finite L-presentation <S | Q_0 | sigma> with sigma(s) = s@1, although R° is not contracting; the partial groups satisfy G_n = G_(n-1) wr M_11, so R° is finitely presented iff sigma(Q_0) lies in the normal closure of Q_0, iff the explicit epimorphism G_0 -> G_0 wr M_11 is injective, and R° embeds in a finitely presented ascending HNN extension
artifacts:
  - experiments/m11-balanced-loop-l-presentation-2026-09-18/rgroup.py
  - experiments/m11-balanced-loop-l-presentation-2026-09-18/l_presentation_checks.py
  - experiments/m11-balanced-loop-l-presentation-2026-09-18/l_presentation_checks.out
distinct_from:
  m11-balanced-loop-host-has-finite-h1: that proves R° is fully self-replicating and bounds H_1(R°); this gives a presentation of R°, reduces its finite presentability to one relator inclusion, and uses no homology.
  m11-balanced-loop-host-h1-is-z55: that computes H_1(R°) = Z/55 by a descent to pure powers and shows homology is silent in degree 2; this runs a similar weight descent on relators rather than on cycles, and turns it into a presentation.
  fp-self-similar-groups-have-fp-ray-loop-subgroups: that is an obstruction to finite presentation through loop subgroups, which is silent for R° (its loops are C_55, Z and 1); this is a criterion, an equivalence, for R° in particular.
  m11-odometer-free-host-is-not-finitely-presented: that decides finite presentation of R'' negatively through its loop subgroup; for R° the loop obstruction is silent, and this leaves the decision as one explicit inclusion question.
  bounded-last-section-ascending-hnns-satisfy-boone-higman: that embeds ascending HNN extensions of bounded (contracting) automaton groups in finitely presented simple groups; the ascending HNN extension here is of a non-contracting group of exponential activity, and only its finite presentation is proved.
---

**ESTABLISHED (unreviewed).** Proof: `m11-balanced-loop-host-has-exact-finite-l-presentation-proof`.
The proof is by hand. The script builds the words `σ(s)` and the finite set `Q_0`, checks
every word exactly in `R°`, and runs the weight descent of Theorem A on sample relators. It
does **not** decide whether `σ(Q_0) ⊆ ⟨⟨Q_0⟩⟩`, so whether `R°` is FP_2 is still open.

**Setting.** As in `m11-balanced-loop-host-has-finite-h1`. We use right actions:
`(xw)^g = x^{π_g} w^{g|_x}` on `X = {1, …, 11}`.
- `α = (1, …, 11)` and `β = (1,2,3,4,8)(5,10,7,11,6)`, with `⟨α, β⟩ = M_11`.
- `b = (b, α, β, 1, …, 1)`.
- `C = (1, 1, 1, C, bα, C^{-1}, 1, …, 1)`.
- `R° = ⟨α, β, b, C⟩` is fully self-replicating: `g ↦ g@x` (section `g` at `x`, identity
  elsewhere) is an injective endomorphism `ι_x` of `R°`.

**Data.**
- `F` is free on `S = {α, β, b, C}`, and `K = ker(F → R°)`.
- `σ : F → F` is the endomorphism with `σ(s) = W_s`, where `W_s` is an explicit word
  representing `s@1`. The script gives weights (numbers of `b^{±1}, C^{±1}` letters) of
  18, 20, 39 and 10079 for `W_α, W_β, W_b, W_C`.
- `ι_x(w) = τ_x^{-1} σ(w) τ_x`, where `τ_x` is a fixed word in `α, β` with `1^{τ_x} = x`.
- The section map `w ↦ w|_x` is the homomorphism `Ψ : F → F ≀_X Sym(X)` given on letters by
  `b|_1 = b, b|_2 = α, b|_3 = β, C|_4 = C, C|_5 = bα, C|_6 = C^{-1}`, with all other letter
  sections trivial. It is followed by free reduction.
- `Q_0` is the closure under `w ↦ w|_x` of the following finite base set:
  - (R1) a finite presentation of `M_11` on `α, β`;
  - (R0) `b^{55}`;
  - (R2) `b^{-1} ι_1(b) ι_2(α) ι_3(β)` and `C^{-1} ι_4(C) ι_5(bα) ι_6(C^{-1})`;
  - (R3) `[σ(s), ι_2(t)]` for `s, t ∈ S`;
  - (R4) `[σ(s), h]` for `h` in a generating pair of `Stab_{M_11}(1)`;
  - (C2) `W_s|_1 · s^{-1}` and `W_s|_x` for `x ≠ 1`.

  Sections never increase the weight, and a section word has length at most twice its
  weight, so the closure is finite. Apart from R1 it has 48 words and 1 805 338 letters.
  Every word of `Q_0` is trivial in `R°`, and this is checked exactly.
- `K_n = ⟨⟨Q_0 ∪ σ(Q_0) ∪ … ∪ σ^n(Q_0)⟩⟩` and `G_n = F/K_n`. Each `G_n` is finitely
  presented.

**Theorem.**

- **(A) Exactness.** `K = ⋃_n K_n`, so `R° = ⟨S | Q_0 | σ⟩` is a finite L-presentation.
  Moreover each `w ∈ K` lies in `K_h`, where `h` is the height of its section descent tree.
  That tree is finite, and its leaves are words in `α, β` or free powers `b^{55j}`.
- **(B) Level shift.** For `n ≥ 1` the map `Φ_n : w ↦ ((w|_x K_{n-1})_x ; π_w)` induces
  `G_n ≅ G_{n-1} ≀_X M_11`. Moreover `K_{n+1} = K_n ⟺ K_n = K_{n-1}`, so the chain `(K_n)`
  is either constant or strictly increasing.
- **(C) Criterion.** The following are equivalent:
  - `R°` is finitely presented;
  - `σ(Q_0) ⊆ ⟨⟨Q_0⟩⟩`;
  - `R° = ⟨S | Q_0⟩`;
  - the epimorphism `θ = Φ_1 : G_0 ↠ G_0 ≀_X M_11` is injective.

  If `R°` is not finitely presented, then in the tower `G_0 ↠ G_1 ↠ G_2 ↠ …` no map is
  injective. The groups are finitely presented, `G_n ≅ G_0 ≀ M_11 ≀ ⋯ ≀ M_11` with `n`
  wreath factors, and the direct limit of the tower is `R°`.
- **(D) Embedding.** `Γ = ⟨S, t | Q_0, t^{-1} s t = σ(s) (s ∈ S)⟩` is finitely presented.
  It is the ascending HNN extension `R° *_{ι_1}`, so `R°` embeds in a finitely presented
  group.

**Scope.** Bartholdi's theorem gives finite L-presentations for contracting regular branch
groups. `R°` is neither contracting nor of bounded activity. Exactness here comes instead
from the letter-weight descent: stable paths end in pure powers `b^j` or `C^j`. This is the
presentation-level form of the `H_1` descent in `m11-balanced-loop-host-h1-is-z55`.

Theorem C turns "is R° FP_2?" into a single inclusion between explicit finite sets. It cannot
be decided by the homological screens, which are silent in degree 2. A negative answer has a
concrete certificate: a group `H` and a map `F → H` that kills `Q_0` but not some `σ(q)`.
