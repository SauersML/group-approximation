---
rg: 2
id: b3-deligne-boundary-is-nonsingular-rank-three-is-not
kind: claim
title: B_3 modulo its centre acts on its Deligne boundary by local prefix replacements, while every irreducible finite-type Artin group of rank at least three has singular boundary points
distinct_from:
  automatic-groups-embed-in-corner-germ-extensions: that is the open general premise, a finite germ extension over the boundary Thompson group of an automatic structure; this computes the singular set for the Deligne structure of finite-type Artin groups, which is empty for B_3 and nonempty in rank at least three.
  z2-free-z-normal-form-boundary-has-corner-singular-orbits: that computes the singular orbits for Z^2 * Z with its free-product structure; this is the Garside normal form of an Artin group.
  artin-deligne-boundary-actions-are-topologically-free: that proves the boundary actions are faithful; this locates where they are not locally prefix replacements.
---

**ESTABLISHED** (lane proof by a finite table and an elementary word argument, not
reviewed; no priority claimed).

## Setting

- `A` is of finite type, and `λ_y` is the action of a simple element `y` on positive
  boundary points.
- `λ_y` is Charney's left-multiplication transducer (BBCMP, proof of Theorem 2.4,
  case (1)). On input `z_1 z_2 ⋯` with state `y_0 = y`, it outputs
  `z'_i = pref(y_{i-1} z_i)` and moves to the state `y_i = z'^{-1}_i y_{i-1} z_i`.
- **Two stable states.** The state `1` stays `1`, and the output then copies the
  input. The copy state `y_i = z_i` also persists: `z_i → z_{i+1}` gives
  `pref(z_i z_{i+1}) = z_i` and next state `z_{i+1}`, so the output is the input
  delayed by one letter.
- **Prefix replacements.** Suppose the state is `1` or the copy state after `r` letters.
  Then on the cylinder of `z_1⋯z_{r+1}`, `λ_y` is a prefix replacement with the same
  tail. The two prefixes end in the same letter, so they have equal follower sets
  `T(z_{r+1})`.
- `B(L̄)` is the boundary Thompson group of `automatic-groups-embed-in-corner-germ-extensions`.
  `L̄` and `∂L̄` are from `artin-groups-mod-central-garside-power-are-continuous-automatic`.

## Statement

1. **B_3 is nonsingular.** Let `A = B_3 = ⟨a, b⟩`.
   - Every simple element `y` reaches state `1` or the copy state within `n + 2` input
     letters, where `n` is the number of leading `Δ`'s of the input.
   - Consequently `Ā = B_3/⟨Δ^2⟩ = PSL_2(Z)` acts on `∂L̄ = {Δ^p q : p ∈ {0,1}}` by
     homeomorphisms that are locally prefix replacements with equal follower sets.
   - So `Ā ≤ B(L̄)`, and the singular set is empty.
2. **Rank at least three is singular.** Let `A` be irreducible of rank at least three,
   and let `s ≠ t` be commuting atoms. Put `x = st`, so that `x → x`.
   - `λ_s` fixes `x^∞`, with the persistent state `s ∉ {1, x}`.
   - `λ_s` is not a local prefix replacement at `x^∞`. The same holds on `∂L̄` and on
     `∂L`.

## Proof

1. **B_3.** Simples are `1, a, b, ab, ba, Δ`, with `aba = bab = Δ`. The table below gives
   `(y, x) ↦ (pref(yx), new state)` for `y, x ∈ {a, b, ab, ba}`. The rows for `b` and
   `ba` follow by the symmetry `a ↔ b`.

   | y \ x | a | b | ab | ba |
   |---|---|---|---|---|
   | a  | (a, a) copy | (ab, 1) | (a, ab) copy | (Δ, 1) |
   | ab | (Δ, 1) | (ab, b) copy | (Δ, b) | (ab, ba) copy |

   Two further rules:
   - `y = Δ` gives `(Δ, x)`, which is copy.
   - Input `x = Δ` gives `(Δ, τ(y))`.

   The only other entry is `(ab, ab) ↦ (Δ, b)`, and its symmetric `(ba, ba) ↦ (Δ, a)`.
   - After `ab`, the next input lies in `{b, ba}`.
   - From state `b` both of these inputs give the copy state: `(b,b) ↦ (b, b)` and
     `(b,ba) ↦ (b, ba)`.
   - So within `n + 2` letters the state is `1` or copy, and by compactness `λ_y` is a
     finite union of prefix replacements on `∂A^+ ∖ [Δ^{n+1}]`.

   On `∂L̄`, a generator `s` acts on `Δ^p q` in three steps:
   - it runs `λ_{τ^p(s)}` on `q`;
   - it strips a produced leading `Δ`, which is decided by the first output letter;
   - it reduces the exponent mod 2.

   Since `n ≤ 1` here, each piece is a prefix replacement. After refining by one letter,
   the two prefixes end in the same letter and so have equal follower sets.
2. **Rank at least three.**
   - **Setup.**
     - `x = st` is simple, with `Start(x) = Fin(x) = {s,t}`. So `x → x`, `x → s` and
       `x → t`.
     - The simple divisors of `s x = sst` are `s, t, st`, so `pref(sx) = st`.
     - The new state is `(st)^{-1} s st = s`, by commutation, so `s` persists along
       `x^∞`.
   - **The germ is not a prefix replacement.** Suppose `λ_s` agreed near `x^∞` with
     `x^N u ↦ x^{N'} u`. Compare two families of points near `x^∞`.
     - For `x^n t^∞`: `s·t^∞ = (st) t^∞`, since `st` is simple. So
       `λ_s(x^n t^∞) = x^{n+1} t^∞`, which forces `N' = N + 1`.
     - For `x^n s^∞`: `s·s^∞ = s^∞`, the copy state. So `λ_s(x^n s^∞) = x^n s^∞`, which
       forces `N' = N`.
     - These are incompatible. The points lie in `Q`, so the same computation applies in
       `∂L̄` and in `∂L`. ∎

## Reading (lane)

- **For B_3.** Item 1 is the base case of the germ-extension route, with no singular
  points at all. `B_3 ≤ Ā × Z` via `(quotient, length)`, and `Ā ≤ B(L̄)`.
  - `B(L̄)` is the topological full group of the shift-of-finite-type groupoid on
    `ΔQ ⊔ Q`. The prefix replacement `Δx ↦ x` makes it Kakutani equivalent to the
    groupoid of the irreducible, aperiodic Deligne graph on `{a, ab, b, ba}`, with edges
    `a → a, ab`; `ab → b, ba`; `b → b, ba`; `ba → a, ab`.
  - Matui's theorems for irreducible one-sided shifts of finite type should then make
    it `F_∞`, with simple commutator subgroup of finite index. That would reprove
    Boone--Higman for `B_3`, which is already known. This transfer was not checked
    here.
- **For rank at least three.** Item 2 shows that the singular set is never empty. The
  singular germ groups contain the commuting pair of germs of `s` and `t` at `(st)^∞`,
  over the lag germs of `x`. This is the corner pattern of
  `z2-free-z-normal-form-boundary-has-corner-singular-orbits`.
- **What is left open.** Whether the singular set is finite modulo `B(L̄)`, and whether
  the germ groups satisfy (E4). Both are open.

## Lesson for general BH

- **Singular germs come from flats.** Singular germs of a Garside boundary action are
  persistent transducer states. A state persists along a periodic tail `x^∞` only if it
  is carried by conjugation, as with the commuting atoms `s` and `t` here. So the
  singular set sees exactly the input's flats.
- **Where a V-type host suffices.** Groups whose quotient by the centre has no `Z^2`,
  such as `B_3` (hyperbolic after dividing by the centre), land inside a V-type
  boundary Thompson group with no singular points.
- **Rank at least three.** Every rank at least three type produces corner germ groups
  that contain `Z^2`. This is the same lesson as `bh-free-36`: hosts must match the
  rank of the input's flats.
- **Suggested next step.** Code each commuting parabolic by a separate colour of a
  higher-rank graph. The persistent state `s` along `(st)^∞` would then become a
  colour-`s` shift, which is a regular prefix replacement in a 2-graph. This is only a
  suggestion; it was not carried out here.
