---
rg: 2
id: m11-linear-activity-self-replicating-group
kind: claim
title: R = <M_11, a, b, c> with a an 11-letter odometer and c = (c, a, 1, ..., 1) is a non-contracting, linear-activity, amenable, fully self-replicating group with root image M_11; its canonical L-presentation presents a self-replicating cover with b_1 >= 2, which is therefore not finitely presented, so R is finitely presented only if a relator outside that L-presentation kills a character
artifacts:
  - experiments/noncontracting-m11-host-2026-09-17/m11_linear_activity_host.g
  - experiments/noncontracting-m11-host-2026-09-17/m11_linear_activity_host.out
distinct_from:
  tits-hosts-for-transitive-local-actions: that builds the bounded instance <M_11, b>, which is contracting and so not finitely presented by Bartholdi's theorem; this adds a linear-activity generator, so the group is not contracting and Bartholdi's theorem no longer applies, and it replaces that theorem by an explicit L-presentation cover whose kernel is the only way left to a finite presentation.
  self-wreathing-groups-have-full-sigma-invariants: that proves character, Sigma and L2 invariants are blind for every R = R wr_X P; this is one concrete non-contracting candidate, and it locates the remaining question in the kernel of an L-presented cover.
  fully-self-replicating-fp-infinity-groups-are-acyclic: that proves b_1 <= 1 for every finitely presented R = R wr_X P with root image in Alt(X); this applies it to the canonical L-presented cover of one explicit group, where b_1 >= 2 is computed by hand.
---

**ESTABLISHED (unreviewed).** Proof: `m11-linear-activity-self-replicating-group-proof`.
The level identities, the rigid-stabilizer certificate, the orders and the activity counts
are checked in the attached GAP script.

**Setting.** Let `X = {1, …, 11}` with the natural action of
`P = M_11 = Stab_{M_12}(12)`. Actions are on the right: `(x w)^g = x^{π_g} w^{g|_x}`.
Let `α = (1, 2, …, 11) ∈ M_11`, and let `β = (1,2,3,4,8)(5,10,7,11,6)`, the element of
order 5 printed by the script. `P` acts on `X*` by acting on the first letter only.
Put

- `a = (a, 1, …, 1) α`, an 11-letter odometer;
- `b = (b, α, β, 1, …, 1)`, the generator of `tits-hosts-for-transitive-local-actions`
  item 6;
- `c = (c, a, 1, …, 1)`, with trivial root permutation.

Let `R = ⟨M_11, a, b, c⟩ ≤ Aut(X*)`. Let `S` be two generators of `M_11` together with
`a, b, c`, and let `F = F(S)` be the free group, with `R = F/N`.

**Theorem.**

1. **Fully self-replicating.** `R` is self-similar with root image `M_11`, and it contains
   `R@x` for every `x ∈ X`. So the section map is an isomorphism `ψ : R ≅ R ≀_X M_11`.
2. **Not contracting.**
   - `a` and `c` have infinite order. On `X^n` their orders are `11^n` and `11^{n−1}`.
   - `(c^m)|_{1^k} = c^m` for all `m, k`. So every power of `c` lies in any nucleus, and
     no finite nucleus exists.
   - `b` has order `55`.
3. **Activity and amenability.**
   - The elements of `M_11` have activity `0`.
   - `a` and `b` are bounded, with `1` and `3` active sections at every level.
   - `c` has exactly `n + 1` active sections at level `n`, so its activity is linear.
   - Hence `R` is amenable, by Amir--Angel--Virág (linear-activity automaton groups are
     amenable; cited), and has no non-abelian free subgroup.
4. **Tits host.** By `tits-hosts-for-transitive-local-actions` item 4, the group
   `Γ⁺_R = (R ≀ M_12) *_{R × R} (R ≀ M_12)` on `T_{12}` is a finitely generated simple
   Tits-(P) group with local action `M_12` and amenable edge groups `R × R`.
   `Γ⁺_R` is finitely presented iff `R` is.
5. **Canonical L-presentation.** Let `σ : F → F` be the endomorphism sending each
   generator `s` to a fixed word for `s@1` (given in the proof). Let `Q_0` be the finite
   set made of:
   - the relators of `M_11`;
   - the commutators `[q, σ(s)]`, for `q` in a generating set of `Stab_{M_11}(1)` and `s ∈ S`;
   - the commutators `[σ(s), p^{-1} σ(s') p]`, for `s, s' ∈ S` and a fixed `p_y ∈ M_11`
     with `1^{p_y} = y`, for each `y ≠ 1`.

   Then:
   - (a) `N = ⟨⟨Q_0 ∪ σ(N)⟩⟩`.
   - (b) Put `L = ⟨⟨⋃_{n ≥ 0} σ^n(Q_0)⟩⟩ ⊆ N` and `G = F/L`, a finitely L-presented
     group. The formal section map makes `G ≅ G ≀_X M_11`, compatibly with `ψ`.
   - (c) The kernel `K = N/L` of `G ↠ R` satisfies `K ≅ K^X`. It is the kernel of the
     action of `G` on `X*`, so either `K = 1` or `K` is infinite.
6. **The cover has two independent characters.** Every assignment of integers to `a` and
   `c`, with `b` and `M_11` sent to `0`, extends to a homomorphism `G → ℤ`. So
   `dim_ℚ H_1(G; ℚ) ≥ 2`, and **`G` is not finitely presented** by
   `fully-self-replicating-fp-infinity-groups-are-acyclic` item 3(d). This is the
   L-presentation signature of the brief: the L-presentation is not equivalent to any
   finite one. The reason here is homological, and no contraction is used.
7. **Dichotomy for `R`.**
   - If `K = 1`, then `R = G` is not finitely presented.
   - If `R` is finitely presented, then `b_1(R) ≤ 1`. So some relator `w ∈ N ∖ L` has
     nonzero exponent-sum vector in `(a, c)`: a relation of `R` kills a character of the
     cover.

   In either case, `b_1(R) ≥ 2` would already show that `R` is not finitely presented.

**Status of the known obstructions for `R`.**

- **Bartholdi (contracting regular branch groups are not finitely presented).** It does not
  apply, by item 2. Its role is taken by item 6: the cover `G` is infinitely presented, but
  `G = R` is not known.
- **Congruence quotients and retracts.** They are blind by item 7 of
  `tits-hosts-for-transitive-local-actions`, since `M_11` is superperfect.
- **Characters, Bieri--Strebel, Σ^n and L².** They are blind by
  `self-wreathing-groups-have-full-sigma-invariants`.
- **Ordinary homology.** `fully-self-replicating-fp-infinity-groups-are-acyclic` needs
  `b_1(R) ≤ 1`. Only `a` and `c` can have infinite order in `H_1(R)`, since `M_11` is
  perfect and `b` has finite order. So `b_1(R) ∈ {0, 1, 2}`, and this is not decided here.
- **Amenability, and no free subgroups.** Neither obstructs finite presentation.

**What is left.** Compute `b_1(R)`, or equivalently decide whether the characters `χ_a`
and `χ_c` of the cover (item 6) vanish on `K`.

- `b_1(R) = 2` kills `R` outright.
- `b_1(R) ≤ 1` needs an explicit relation of `R` with nonzero `a`- or `c`-exponent sum.
  Such a relation lies outside `L`, so it is an element of `K`: a word acting trivially on
  the tree that the recursion does not see. After that, the only remaining tools are ones
  that see the relators themselves, such as Dehn-function or asymptotic-cone arguments.

**Calibration.**

- Removing `c` gives `R_0 = ⟨M_11, a, b⟩`, and removing `a` as well gives
  `⟨M_11, b⟩` of `tits-hosts-for-transitive-local-actions`. Both are bounded automaton
  groups, so they are contracting and not finitely presented, by Bartholdi (cited).
- The proof of items 5 and 6 applies verbatim to `R_0`, giving a cover with `b_1 ≥ 1`.
  That is consistent: the acyclic node forbids `b_1 ≥ 2` only.
- The GAP script recomputes the w7-030 rigid-stabilizer certificate with all
  `h_q`, `q ∈ Stab_{M_11}(1)`, and gets `|⟨h_q⟩| = |M_11|^{10}`.
