---
rg: 2
id: ct-z-conjugacy-problem-is-undecidable
kind: claim
title: Kohl's class transposition group CT(Z) has undecidable conjugacy problem, already for explicit pairs of words in CT_{3,5,7,11,13}(Z) and even when conjugators may be taken from RCWA(Z); this answers Kourovka Problem 21.73 negatively
requires:
  - ct-z-finite-cycle-problems-are-undecidable
  - ct-z-finite-subgroups-are-classified-by-stabilizer-sets
  - ct-p-z-is-a-one-vertex-k-graph-full-group
---

**ESTABLISHED** (lane proof, not reviewed).
- **Proof.** Elementary: valuations and one finiteness count.
- **Input (H).** The universality of reversible counter machines (Morita, TCS 168
  (1996) 303–320). Kari–Ollinger use the same input; Morita's paper was not read at
  source.
- **Priority.** None is claimed. An arXiv search (class transposition,
  residue-class-wise) found no treatment of 21.73. Salo (arXiv:2011.07827) proves the
  analogous theorem for 2V; see `ct-z-finite-subgroups-are-classified-by-stabilizer-sets`
  for why his method cannot transfer.

## Statement

Let `S = {2,3,5,7,11,13}`. An algorithm takes a reversible counter machine `M` and an
initial configuration `x*` of `M` (one with no predecessor). It outputs two words `A_M`,
`B_M` in class transpositions with `S`-smooth moduli such that:

1. If `M` halts from `x*`, then `A_M` and `B_M` are conjugate in `CT_{3,5,7,11,13}(Z)`
   by an explicit involution, itself a word in class transpositions.
2. If `M` does not halt from `x*`, then no `c ∈ RCWA(Z)` has `c A_M c^{-1} = B_M`.

**Input (H).** Halting from an initial configuration is undecidable for reversible
counter machines (Morita 1996 plus Bennett). Any number of counters may be used, one
prime per counter. The two counters below are for notation only.
- **Normal form.** If the start configuration `(q_0, 0, …, 0)` is not already initial,
  add a step counter `c`.
  - For each action `(s, i, φ, t)` of `M`, add a fresh state `t_{s,i,φ,t}`. Route
    `s → t` through it, and from it increment `c` and enter `t`. Do this only for the
    post-patterns of `M`'s instructions with that action.
  - **Reversibility.** By reverse determinism of `M`, a post-pattern at `t` determines
    the action, so the new machine is reversible.
  - **Initial configurations.** Every configuration of a state of `M` with `c = 0` has
    no predecessor.
  - **Halting.** Halting from `(q_0, 0, …, 0)` is unchanged.

**Corollaries.**
- For every group `G` with `CT_{3,5,7,11,13}(Z) ≤ G ≤ RCWA(Z)`, the conjugacy problem
  is undecidable. This includes CT(Z) (Kourovka 21.73) and RCWA(Z).
- The same holds for `CT_{3,5,7,11,13}(Z)`, a finitely presented simple group of type
  `F_∞` (`ct-p-z-is-a-one-vertex-k-graph-full-group`). Its words in class transpositions
  can be rewritten effectively in a finite generating set, because the word problem is
  decidable. So this is a second natural fp simple group with undecidable conjugacy,
  after Salo's `2V`.
- By `ct-z-finite-subgroups-are-classified-by-stabilizer-sets`, the pairs necessarily
  have infinite order.

## The elements

- **Machine.** `M` is a reversible 2-counter machine with states `1..N`, and `x* = (s_0, 0, 0)`
  is initial.
  - A *configuration* is `y = (s, a, b, e, d)`: `(s, a, b)` is an `M`-configuration,
    `e ∈ {0,1}` is a direction (`1` = backward), and `d ∈ {0,1}` is a dummy bit.
  - `Λ(y) = 3^a 5^b 7^s 11^e 13^d`.
- **Codes.** `X` is the set of `n = Λ(y) w` with `w` coprime to `S`, either sign. It is a
  periodic set: `v_2 = 0`, `1 ≤ v_7 ≤ N`, `v_11, v_13 ≤ 1`. The cofactor `w(n)` and
  `y(n)` are read off from the valuations.
- **Switching machine `D`** (Kari–Ollinger Thm 3), a bijection of configurations:
  - Forward (`e = 0`): apply `M`. At a halting `(s,a,b)`, set `e = 1` instead.
  - Backward (`e = 1`): apply `M^{-1}`. At an initial `(s,a,b)`, set `e = 0` instead. If
    moreover `(s,a,b) = x*` (a *touch*), also flip `d`.

  Halting, initial and touch configurations are cells cut out by
  `v_3, v_5 ∈ {0,1,≥2}` and `v_7`. So the map `α(Λ(y)w) = Λ(Dy)w` on `X`, identity
  elsewhere, is a bijection that is piecewise multiplication by elements of
  `3^Z 5^Z 7^Z 11^Z 13^Z`, on classes mod `L = 2·3^2·5^2·7^{N+1}·11^2·13^2`.
- **The twist `T`.** Put `m_0 = 30030 = 2·3·5·7·11·13` and `C = 20020`, so
  `C ≡ 0 mod 10010` and `C ≡ 1 mod 3`.
  - For `Λ` fixed, let `T_Λ` be the product of the class transpositions
    `τ_{Λρ(Λm_0), Λρ'(Λm_0)}`. Here `ρ` runs over residues mod `m_0`, coprime to `S`
    with `ρ ≡ 1 mod 3`, and `ρ' ≡ ρ + C mod m_0`.
  - The pairs `{ρ, ρ'}` are disjoint, and they exhaust the residues coprime to `S`.
  - On codes with this `Λ`, `T_Λ` fixes `y` and replaces `w` by
    `T(w) = w + δ`, where `δ = ρ' − ρ ∈ (−m_0, m_0) ∖ {0}` depends on `w mod m_0`.
    `T(w)` is again coprime to `S`, has the same sign as `w`, and differs from `w` mod 3.
  - Let `T_* = T_{Λ_0} T_{Λ_1}`, with `Λ_d = 7^{s_0}·11·13^d` the two touch
    configurations `(x*, e=1, d)`.
- **The words.**
  - `β = α T_*`. So `β` acts like `α`, except that the cofactor `w` becomes `T(w)` on
    leaving a touch.
  - As in `ct-z-finite-cycle-problems-are-undecidable`, put `s_1 = ∏ τ_{c(L), 2c(2L)}`
    over the classes `c(L) ⊆ X`, and `s_2 = ∏ τ_{2c(2L), α(c(L))}`.
  - `A_M = s_2 s_1`, which is `α` on `X`, `2α^{-1}(·/2)` on `2X`, and the identity
    elsewhere.
  - `B_M = T_*^{(2X)} A_M T_*`, where `T_*^{(2X)} = 2T_*(·/2)`. This is `β` on `X` and
    `2β^{-1}(·/2)` on `2X`.

## Proof of 1 (halting gives an explicit conjugator)

- **Fibre notation.** Write points of `X` as `(y, w)`. Then `α(y,w) = (Dy, w)` and
  `β(y,w) = (Dy, T^{J(y)} w)`, where `J(y) = 1` exactly at the touches.
- **The cycle of `x*`.** Suppose `x* = x_0 → x_1 → … → x_L` is the halting run. Then the
  `D`-orbit of `(x*, e=1, d=0)` is the cycle:
  - the touch, to `(x*, 0, 1)`;
  - the forward run to `(x_L, 0, 1)`;
  - the switch to `(x_L, 1, 1)`;
  - the backward run to `(x*, 1, 1)`;
  - the touch, to `(x*, 0, 0)`;
  - and the same again with `d = 0`.

  It has length `4(L+1)` and contains exactly two touches. The set `Y` of its
  configurations is finite and computable from the run.
- **The conjugator.** Fix a base point `y_0 ∈ Y`. For `y ∈ Y`, let `k(y) ∈ {0,1}` be the
  parity of the number of touches strictly before `y` on the path from `y_0`. This is
  well defined, since the whole cycle has 2 touches. Put `k = 0` off `Y`.
- **The identity.** With `γ(y,w) = (y, T^{k(y)} w)`,
  `γαγ^{-1}(y,w) = (Dy, T^{k(Dy)+k(y)} w) = (Dy, T^{J(y)} w) = β(y,w)`.
  - On `Y` this holds by the choice of `k`.
  - Off `Y`, `J = k = 0` and `D` preserves the complement of `Y`.
- **As a word.** `γ = ∏_{y∈Y, k(y)=1} T_{Λ(y)}` is an involution, and a product of class
  transpositions with `S`-smooth moduli.
- **On the buffer copy.** `γ̃ = γ · 2γ(·/2)` satisfies `γ̃ A_M γ̃^{-1} = B_M`, because
  `γα^{-1}γ^{-1} = β^{-1}`. ∎

## Proof of 2 (non-halting forces non-conjugacy, even in RCWA(Z))

**The special orbit.** Suppose the run from `x*` never halts. Take a cofactor `q ≥ 1`
coprime to `S`, and put `n_0 = Λ(x*,1,0)·q`. Then the `B_M`-orbit
`(n_t)_{t∈Z}` of `n_0` lies in `X`, and:
- for `t ≤ 0`, `n_t = Λ(x_{|t|}, 1, 0)·q`;
- for `t ≥ 1`, `n_t = Λ(x_{t−1}, 0, 1)·T(q)`.

There is exactly one touch, at `t = 0`. The configurations are pairwise distinct, since
the run from an initial configuration never repeats. So `n_{t+1} = ρ_t n_t` for every
`t ≠ 0`, with `ρ_t` in the finite set `R` of step multipliers of `D`.

**Transport by a conjugator.** Let `c ∈ RCWA(Z)` with `c A_M c^{-1} = B_M`. Then
`m_t = c^{-1}(n_t)` is an infinite `A_M`-orbit, so it lies in `X` or in `2X`.
- **Its shape.** Along it, `m_{t+1} = ρ'_t m_t` with `ρ'_t ∈ R ∪ R^{-1}`, since `A_M` is
  multiplicative there. The cofactor `w'` is constant, so `m_t = ±Λ'_t w'`, with the
  `Λ'_t` pairwise distinct `S`-integers.
- **The pieces.** Let `c^{-1}(n) = λ_i n + μ_i` on its finitely many classes, and let
  `i(t)` be the class of `n_t`. For `t ≠ 0`,

      (λ_{i(t+1)} ρ_t − ρ'_t λ_{i(t)}) · n_t = ρ'_t μ_{i(t)} − μ_{i(t+1)}.

**Step 1: eventually the coefficient vanishes.** The tuple
`(i(t), i(t+1), ρ_t, ρ'_t)` ranges over a finite set. When the coefficient is nonzero,
it determines `n_t`, and the `n_t` are distinct. So for `|t| ≥ t_1` the coefficient is
`0`, and `μ_{i(t+1)} = ρ'_t μ_{i(t)}`.

**Step 2: eventually the pieces are linear.** Suppose `μ_{i(t)} ≠ 0` for some
`t ≥ t_1`.
- Then `μ_{i(t+k)} = (Λ'_{t+k}/Λ'_t)·μ_{i(t)}` for all `k ≥ 0`.
- These values are pairwise distinct, but there are only finitely many classes, a
  contradiction.
- So `μ_{i(t)} = 0` for `t ≥ t_1`. Symmetrically, `μ_{i(t)} = 0` for `t ≤ −t_1`.

**Step 3: comparing cofactors.** For `|t| ≥ t_1`, `λ_{i(t)} n_t = m_t`.
- Split `λ_i = λ_i^S λ_i°`, with `λ_i^S` an `S`-unit and `λ_i°` prime to `S`.
- Comparing the `p`-adic valuations for `p ∉ S` gives `λ°_{i(t)} q = ±w'` for
  `t ≤ −t_1`, and `λ°_{i(t)} T(q) = ±w'` for `t ≥ t_1`.
- Hence `T(q)/q = q'` lies in the finite set `{±λ_i°/λ_j°}`, and `q' ≠ 1`.
- So `q = δ/(q' − 1)`, with `δ` and `q'` both ranging over finite sets.

**Conclusion.** Choose `q` outside this finite set; `c` was fixed beforehand. This is a
contradiction, so no conjugator exists. ∎

## Remarks

- **The mechanism: arithmetic rigidity at infinity.** An rcwa conjugator between two
  multiplicative (`S`-unit) dynamics must be multiplicative, i.e. have zero translation
  part, on the far ends of every infinite orbit (Steps 1–2).
  - So the non-`S` part of the cofactor is a conjugacy invariant of each end of an orbit,
    up to finitely many multipliers.
  - A single additive twist `T` at one point of an orbit changes the cofactor between
    the two ends. It can be undone locally exactly when the twisted orbit closes up,
    which happens exactly when the run halts.
- **Contrast with Salo.** Salo's `2V` argument uses blinkers, far-away bits read by a
  bounded conjugator. Here the far-away datum is the `p`-adic cofactor for `p ∉ S`.
  Multiplication can move it only by finitely many ratios.
- **Complexity.** Conjugacy in `CT(Z)` is r.e., by enumerating words and comparing rcwa
  tables. The construction reduces the halting problem to it, so conjugacy in `CT(Z)`
  is Σ⁰₁-complete.

## Lesson for general BH

**Separation.** The finitely presented simple hosts `CT_P(Z)` separate the three Dehn
problems sharply:
- the word problem is trivial;
- the torsion-part conjugacy is decided by stabilizer sets;
- general conjugacy is Σ⁰₁-complete.

A BH embedding into such a host therefore can never be expected to make conjugacy
decidable, and it needs to control only relations.

**Transferable tool: arithmetic rigidity.** Piecewise-affine conjugators must be linear
at the ends of multiplicative orbits. So `S`-adic cofactors are invariants at infinity.
This gives a non-conjugacy and non-embedding test for elements, and plausibly for
subgroups, of RCWA-type hosts. It is the arithmetic counterpart of the symbolic
"bounded conjugator" argument used for `nV`.
