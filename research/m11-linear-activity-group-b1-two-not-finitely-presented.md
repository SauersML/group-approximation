---
rg: 2
id: m11-linear-activity-group-b1-two-not-finitely-presented
kind: claim
title: The non-contracting M_11 group R = <M_11, a, b, c> has H_1(R) = Z^2 + (finite), because the a- and c-exponent sums survive every relation by a section-descent to stable words; so R and its simple Tits host are not finitely presented
artifacts:
  - experiments/m11-germ-characters-2026-09-18/exponent_descent.py
  - experiments/m11-germ-characters-2026-09-18/exponent_descent.out
distinct_from:
  m11-linear-activity-self-replicating-group: that builds R, shows that its canonical L-presented cover G has b_1 >= 2, and leaves open whether some relation of R outside the L-presentation kills a character; this proves no relation of R does, so b_1(R) = 2 and R itself is not finitely presented.
  fully-self-replicating-fp-infinity-groups-are-acyclic: that proves b_1 <= 1 for every finitely presented R = R wr_X P with root image in Alt(X); this supplies the missing input b_1 = 2 for one explicit non-contracting group, so that theorem applies.
  self-wreathing-groups-have-full-sigma-invariants: that proves characters are blind as a finiteness test (Sigma^1 is full for every R = R wr_X P); this uses the characters only through their number, which is what the acyclicity bound sees.
---

**ESTABLISHED (unreviewed).** Proof: `m11-linear-activity-group-b1-two-not-finitely-presented-proof`.
The script decides the word problem of `R` exactly and checks every combinatorial step on
all short words.

**Setting.** The notation is that of `m11-linear-activity-self-replicating-group`:

- `X = {1, …, 11}` and `M_11 = Stab_{M_12}(12)`;
- `a = (a, 1, …, 1) α`, where `α = (1, …, 11)`;
- `b = (b, α, β, 1, …, 1)`;
- `c = (c, a, 1, …, 1)`;
- `R = ⟨M_11, a, b, c⟩`, a fully self-replicating group with `R ≅ R ≀_X M_11`.

Let `F` be the free group on `M_11 ⊔ {a, b, c}`, with `R = F/N`. Let `e_a, e_c : F → ℤ` be
the exponent sums of `a` and `c`.

**Theorem.**

1. **Both exponent sums descend.** `e_a(N) = e_c(N) = 0`. So `g ↦ (e_a(g), e_c(g))` is a
   surjection `R ↠ ℤ²`. Moreover `H_1(R; ℤ) ≅ ℤ² ⊕ ⟨[b]⟩`, with `[b]` of order dividing `55`.
   In particular `b_1(R) = 2`, and `dim_k H_1(R; k) ≥ 2` for every field `k`.
2. **Not finitely presented.** `H_2(R; ℚ)` is infinite-dimensional. So `R` is not of type
   `FP_2` over `ℚ`, and in particular it is not finitely presented. This is items 1 and
   2(i) of `fully-self-replicating-fp-infinity-groups-are-acyclic`: two independent degree-1
   classes give `E_2 ≠ 0`. It is also item 3(d) there, which applies with `d = 11` and root
   image `M_11 ≤ Alt(11)`.
3. **The Tits host dies too.** `Γ⁺_R = (R ≀ M_12) *_{R×R} (R ≀ M_12)` is a finitely
   generated simple Tits-(P) group with amenable edge groups, but it is not finitely
   presented, by item 4 of the target node.
4. **Descent lemma (the method).** Let `R = ⟨P, Q⟩ ≤ Aut(X*)`, where `P` is finitary and
   each state in `Q` has every section in `Q^{±1} ∪ P`. Call a word over `Q^{±1}`
   **stable at `x`** if every letter has a section in `Q^{±1}` at the point where it is
   read. A **stable cycle** is a sequence `w_0, …, w_p = w_0` of words, each `w_i` stable at
   some `x_i`, with `w_{i+1}` the letter-by-letter section `w_i|_{x_i}`. Let `λ : F → ℤ` be
   a homomorphism with `Σ_x λ(w|_x) = λ(w)` for every relation `w`. Suppose `λ` vanishes
   on every relation that lies on a stable cycle. Then `λ` vanishes on `N`.
   - The test is finite in the word length.
   - For `R`, `λ = e_c` satisfies the hypothesis on its own.
   - `λ = e_a` satisfies it once `e_c(N) = 0`.

**Remark: why the brief's germ route falls short (heuristic, not part of the theorem).**
The germ cocycle along the rays with tail `1^ω` sees `e_c`: each `c^{±1}` has exactly one
non-trivial germ class there. It does not see `e_a` in any obvious way. The reason is that
`c = ∏_{j≥0} a@(1^j 2)` spreads infinitely many `a`-germs along `1^ω`, so a
finitely supported sum over germs cannot separate `a` from `c`. The descent in item 4 does
not use germs, and it reaches both characters.

**Calibration.**

- **Bounded subgroup.** Proposition 5 of the proof, with no `c`-letters, shows that `e_a`
  is also a character of the bounded subgroup `R_0 = ⟨M_11, a, b⟩`.
- **Odometer.** For the one-state odometer the descent gives its character `ℤ`.
- **Level quotients.** The level quotients `R_n = M_11 ≀ ⋯ ≀ M_11` are perfect. So no
  finite-quotient computation can detect either character; this is why an exact word
  solver was needed.
- **Script.** It decides triviality exactly, by a finite section closure. It recovers
  the relations `[a@1, a@2] = [c@1, a@2] = 1`, `q^{-1} c q = c` for
  `q ∈ Stab_{M_11}(1, 2)`, and `b^{55} = 1`. It rejects `a^{11}`, `c^{11}`, `b^{11}` and
  `[b, c]`. It checks the mass identities, the length bound and the stable-word bound
  `|e_a| ≤ 1` on all short words. It finds that all 12 relations of length at most 6
  over `{a, b, c, α, β}^{±1}` have both exponent sums `0`.

**What is left for the Tits route of `boone-higman-conjecture`.**

- **This candidate is dead.** Under item 3(d), a finitely presented `R ≅ R ≀_X P` with
  root image in `Alt(X)` and `|X| ≥ 4` needs `b_1(R) ≤ 1`. Every group built like this one
  fails that as soon as two infinite-order states carry independent exponent
  characters.
- **What the next candidate needs.** It needs relations that are stable and carry
  exponent mass: stable section-cycles `w = w|_x` with `λ(w) ≠ 0`. For `a`, stability
  forces the `a`-letters to alternate in sign, because `a`'s only active letter `1` is
  moved by its root permutation. So:
  - a candidate needs an infinite-order state whose root permutation fixes its active
    letter, or has several active letters;
  - Lemma 2 of the proof gives a finite test for such a design before any presentation
    work is done.
