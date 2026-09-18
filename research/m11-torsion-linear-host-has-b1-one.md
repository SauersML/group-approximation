---
rg: 2
id: m11-torsion-linear-host-has-b1-one
kind: claim
title: Giving the linear generator the balanced section g = a@1 (a@2)^-1 makes c torsion in homology (the product of its eleven b-conjugates is trivial), so R' = <M_11, a, b, c> is a non-contracting fully self-replicating group with b_1 = 1 that passes the acyclicity bound at FP_2; any odometer state keeps b_1 >= 1 and blocks FP_10, and the section-exponent matrix must act unimodularly on H_1
artifacts:
  - experiments/m11-torsion-linear-host-2026-09-18/torsion_linear_host.py
  - experiments/m11-torsion-linear-host-2026-09-18/torsion_linear_host.out
distinct_from:
  m11-linear-activity-group-b1-two-not-finitely-presented: that proves b_1 = 2 for c = (c, a, 1, ..., 1), which kills that group; this changes the section of c to the balanced element g, finds a stable relation with nonzero c-exponent, and gets b_1 = 1, which the acyclicity bound allows.
  m11-linear-activity-self-replicating-group: that builds the linear-activity candidate with an L-presented cover of b_1 >= 2; this is a different group, with a different linear generator, whose b_1 is computed exactly and equals 1.
  fully-self-replicating-fp-infinity-groups-are-acyclic: that bounds b_1 <= 1 for finitely presented R = R wr_X P; this proves a separate integral constraint (the section map acts on H_1(R; Z) as an automorphism, so only unit-constant factors of the section-exponent polynomial can carry characters), and exhibits a non-contracting candidate meeting the bound.
---

**ESTABLISHED (unreviewed).** Proof: `m11-torsion-linear-host-has-b1-one-proof`.
The script decides the word problem of `R'` exactly and checks the relation, the mass
identities and the stable-word bound.

**Setting.** The notation is that of `m11-linear-activity-self-replicating-group`:
`X = {1, …, 11}`, `M_11 = Stab_{M_12}(12)`, `α = (1, …, 11)`, and `β` of order 5.
Actions are on the right. Put

- `a = (a, 1, …, 1) α`, the odometer;
- `b = (b, α, β, 1, …, 1)`;
- `g = a@1 · (a@2)^{-1} = (a, a^{-1}, 1, …, 1) = a α^{-1} a^{-1} α`;
- `c = (c, g, 1, …, 1)`, with trivial root permutation.

Let `R' = ⟨M_11, a, b, c⟩`. The only change from the dead candidate of
`m11-linear-activity-group-b1-two-not-finitely-presented` is the section of `c` at `2`:
it is now `g`, which has `a`-exponent `0`, instead of `a`.

**Theorem.**

1. **Candidate.** `R'` is fully self-replicating with root image `M_11`, so
   `R' ≅ R' ≀_X M_11`. It is not contracting: `c^m|_1 = c^m` and `c^m|_{21} = a^m`, so
   `c` has infinite order. It has linear activity, so it is amenable
   (Amir–Angel–Virág; cited). Its Tits host `Γ⁺_{R'} = (R' ≀ M_12) *_{R'×R'} (R' ≀ M_12)`
   is a finitely generated simple Tits-(P) group. It is finitely presented iff `R'` is.
2. **The relation.** `U = ∏_{k=0}^{10} b^{-k} c b^k` is trivial in `R'`, and
   `e_c(U) = 11`. So `11 [c] = 0` in `H_1(R'; Z)`.
3. **Homology.** `H_1(R'; Z) ≅ Z[a] ⊕ T`, where `T = ⟨[b], [c]⟩` is finite and its order
   involves only the primes `5` and `11`. So `b_1(R') = 1`. The `a`-exponent sum
   survives, by the stable-cycle descent of the dead node.
4. **Where `R'` stands against the known obstructions.**
   - **FP_2 is unobstructed.** The acyclicity bound `b_1 ≤ 1` (item 3(d) there) holds. One
     odd class in degree 1 gives no excess `E_2`, so that theorem forces nothing in
     `H_2`. Bartholdi's theorem does not apply, since `R'` is not contracting.
     Characters, Σ-invariants and L² invariants are blind for all such groups
     (`self-wreathing-groups-have-full-sigma-invariants`). Congruence quotients are
     blind too, since `M_11` is superperfect.
   - **FP_10 fails.** `H_1(R'; Q) ≠ 0` and `M_11 ≤ Alt(11)`. So `H_{10}(R'; Q)` is
     infinite-dimensional (item 3 of `fully-self-replicating-fp-infinity-groups-are-acyclic`),
     and `R'` is not of type `FP_10`.
5. **Odometer obstruction (a whole class).** Let `R = ⟨P, Q⟩` be fully self-replicating,
   with `P` finitary, and with every letter section of every `s ∈ Q` in
   `Q^{±1} ∪ P ∪ {∅}`. Suppose some `a ∈ Q` has one non-finitary section, namely `a`
   itself at a letter `x_a` moved by its root `π_a`. Suppose every other state in `Q` has
   trivial root and sections of total `a`-exponent `0`. Then `e_a` descends to a
   surjection `R ↠ Z`. With root image in `Alt(X)` and `|X| ≥ 3`, `R` is therefore not
   `FP_{|X|−1}` and not `FP_∞`. Every candidate built on the `M_11` odometer this way,
   including `R'`, lies in this class.
6. **Unimodular screen (a finite test on the design).** Let `R = ⟨P, Q⟩ ≤ Aut(X*)` be
   fully self-replicating with perfect root image `P`, and let `P` act on the first letter
   only. Write each section `s|_x` of `s ∈ Q` as a word over `P ∪ Q`. Let
   `μ ∈ M_Q(Z)` be the matrix with `μ_{s,t}` the total `t`-exponent of the words `s|_x`,
   summed over `x`. Then:
   - the section-sum map `[r] ↦ Σ_x [r|_x]` is an automorphism of `H_1(R; Z)`;
   - on `H_1(R; Q)` it is a quotient of `μ` by a `μ`-invariant subspace;
   - so `b_1(R)` is at most the total degree, counted with multiplicity, of the
     irreducible factors `f` of `det(t − μ)` over `Q` with `f(0) = ±1`.

   Examples:
   - The designs above have `(t − 1)^3` or `t(t − 1)^3`, so the screen allows up to 3 and
     the finer descent is needed.
   - An odometer-free design `z = (z, h, 1, …)`, `h = (z, z, z, 1, …) α` has the
     irreducible `t² − t − 3`. So **if** it is fully self-replicating, then `b_1 = 0`.

**What is left for the Tits route of `boone-higman-conjecture`.**

- **`R'` is the first non-contracting fully self-replicating `M_11` group that passes
  every known obstruction to finite presentation.** Deciding whether `R'` is finitely
  presented, or the same question for a relative of it, would settle whether this route
  gives a finitely presented simple Tits host.
  - The question is now about the relators themselves: the kernel of the canonical
    L-presented cover, `K = K^X`.
  - `FP_∞` is out for `R'` by item 4.
- **A candidate that could be `FP_∞`** must avoid item 5. So it has no odometer state,
  and its infinite order comes from states with several active letters. Item 6 is the
  design rule for such a candidate: it needs no unit-constant factor in `det(t − μ)`.
  Full self-replication of the `z, h` design is the next check.

**Calibration.**

- With `c = (c, a, 1, …)`, the same word `U` is **not** trivial (the script checks this).
  That matches `b_1 = 2` there: `U|_2 = ∏ α^{-k} a α^k` has `a`-exponent `11`.
- For the bounded group `⟨A_5, b⟩` of `fully-self-replicating-tree-groups-give-fg-tits-hosts`,
  with `b` of order 15, the matrix is `(1)`. The screen allows `b_1 ≤ 1`, and the true
  value `0` is consistent with it.
- For the dead candidate `R`, the screen gives `(t − 1)^3`, which allows the true value
  `b_1 = 2`.
- The finitary group `Fin(M_11)` has `Q = ∅`. The screen gives `b_1 = 0`, which is
  correct.
