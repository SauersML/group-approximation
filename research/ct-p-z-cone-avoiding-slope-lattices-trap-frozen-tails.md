---
rg: 2
id: ct-p-z-cone-avoiding-slope-lattices-trap-frozen-tails
kind: claim
title: "If no product of slopes of a finitely generated G ≤ CT_P(Z) is an integer other than 1 (e.g. slopes in ⟨3/2, 5/2⟩), a positive weighted level is conserved, every frozen tail is trapped on a finite level set, frozen points have orbits bounded by the frozen degree, Kourovka 20.44 holds whenever some point has a frozen tail, and G is finite iff it has finitely many slopes iff every point has a frozen tail"
distinct_from:
  ct-p-z-mixed-ray-frozen-tails-force-finite-orbits: that is the rank-one mixed-sign case; this is every rank, under the cone-avoidance hypothesis, which is the exact condition that makes the trapping argument work.
  ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits: that proves the finiteness criterion on a mixed ray; this extends it to cone-avoiding slope lattices of any rank.
  ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44: that is the opposite extreme, where all slopes are powers of one integer.
---

**ESTABLISHED** (lane proof; **Referee PASS** bh-ref-q11 2026-09-19 for Lemmas 1–2 and item 3; items 1, 2, 4 rest on the mixed-ray nodes). No priority claimed. It carries out the first step of the
*slope-lattice cone conjecture* stated below.
- **What stays open.** Kourovka 20.44 and 19.46 (S. Kohl) in the totally consumable (sweeping)
  case, exactly as on a mixed ray.

## Setting

- **Notation.** `P` is finite, `S = P ∪ {2}`, and degrees are `n ∈ N^S` with `m_n = ∏ p^(n_p)`.
  For a slope `q` write `ν(q) = (v_p(q))_p ∈ Z^S`.
- **The slope lattice** of `G = ⟨S_0⟩` is `Λ(G) = ⟨ν(q) : q a slope of a piece of a generator⟩`.
  It contains `ν(q)` for every slope `q` of every element of `G`, by the cocycle identity.
- **Cone-avoiding.** `Λ` is *cone-avoiding* if `span_R(Λ) ∩ R^S_(≥0) = {0}`.

## Lemma 1 (three equivalent forms)

For a lattice `Λ ⊆ Z^S` the following are equivalent:
- (i) `Λ` is cone-avoiding;
- (ii) `Λ ∩ N^S = {0}`, i.e. no product of slopes of `G` is an integer other than `1`;
- (iii) there is `w ∈ Z^S` with every `w_p ≥ 1` and `w · λ = 0` for all `λ ∈ Λ`.

Under (iii) the *weighted level* `ℓ_w(n) = w · n` of every tracked degree is conserved.

*Proof.*
- **(i) ⇒ (ii).** Immediate.
- **(ii) ⇒ (i).** A nonzero point of the rational polyhedral cone `span_Q(Λ) ∩ Q^S_(≥0)` has a
  multiple in `Λ`, since `Λ` has finite index in `span_Q(Λ) ∩ Z^S`.
- **(i) ⇔ (iii).** This is Stiemke's theorem of the alternative: a subspace `L` meets the closed
  positive orthant only in `0` iff `L^⊥` contains a strictly positive vector. Rationality of `L`
  lets one take `w` integral. ∎

## Lemma 2 (trapped level sets)

If `Λ` is cone-avoiding with weight `w`, then for every `n ∈ N^S` the set
`Seg(n) = (n + Λ) ∩ N^S` lies in the finite box `{p : 0 ≤ p_q ≤ ℓ_w(n)/w_q}`. Hence
`A(n) = Σ_{p∈Seg(n)} m_p` is finite and computable.

*Proof.* For `p ∈ Seg(n)`, `w · p = w · n`, and every term `w_q p_q` is nonnegative. ∎

## Theorem

Let `G ≤ CT_P(Z)` be finitely generated with cone-avoiding `Λ(G)`. Tails, reading, frozen degrees
and the potential are as in the mixed-ray nodes.
1. **Frozen tails force finite orbits.** If `n` is frozen at `x ∈ Ẑ`, then `|G·x| ≤ A(n)`.
2. **Kourovka 20.44 where something freezes.**
   - If some point of `Ẑ` has a frozen degree `n`, then `G` has infinitely many orbits on `Z`.
   - Its orbit minima in `[0, N]` number at least `δ_n N / (2A(n))` for `N ≥ M_n`, where
     `δ_n ≥ 1/M_n`, and likewise on `[−N, −1]`.
3. **Finiteness criterion.**
   - For **every** finitely generated `G ≤ CT_P(Z)`, whatever `Λ`, `G` is finite iff it has
     finitely many slopes. A bounded cocycle freezes a common degree `n`, and the tracked shifts
     then lie in a finite box. This strength was noted by bh-ref-q11.
   - Under cone-avoidance both conditions are also equivalent to: every point of `Ẑ` has a frozen
     tail.
4. **Periodic groups.** If `G` is periodic, the potential is well defined on orbits. Then `G` is
   infinite iff some orbit has unbounded potential, i.e. its tails sweep every level set they meet.

*Proof.* The proofs of `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits` (items 1–2) and
`ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits` (items 1–2) use the ray hypothesis in one
place only: the finiteness of `Seg(n)`. Lemma 2 supplies it here. Everything else is unchanged:
- uniform shift of unread degrees by the cocycle, now in `Λ`;
- reversal by inverse tables;
- prefix dependence and clopen `Y_n`;
- the orbit bound `ρ + m_p z` with `p ∈ Seg(n)`;
- compactness, and the finite-index intersection of stabilizers;
- trivial torsion germs.

In (3), "bounded cocycle ⇒ frozen everywhere" takes `n` with every
`n_q ≥ D + max_(λ∈B) |λ_q|` over the finite set `B` of cocycle values. ∎

**The hyperbolic-return lemma** of the mixed-ray torsion node transfers only for returns whose drift
`δ ∈ Λ ∖ {0}` has no zero coordinate. In a cone-avoiding lattice every nonzero `δ` has mixed signs,
but zero coordinates are possible.

## Examples

- **Trapped.**
  - `⟨3/2, 5/2⟩ ⊆ CT_{{3,5}}(Z)`: `Λ = ⟨(−1,1,0), (−1,0,1)⟩` and `w = (1,1,1)`. The level
    `e_2 + e_3 + e_5` is conserved.
  - `⟨3/2, 5/3⟩`: again `w = (1,1,1)`.
  - Every mixed-sign ray `(a/b)^Z` with `a, b > 1` coprime.
- **Not trapped.**
  - Kohl's `G_T`: its slopes include `2`, so `(1, 0) ∈ Λ`.
  - Conway's amusical permutation (slopes `3/2`, `3/4`): `Λ = Z^2 ∋ (1, 0)`.
  - Every positive ray: `Λ = Zv` with `v ≥ 0`.

## The slope-lattice cone conjecture (refined)

Let `C_Λ = span_R(Λ) ∩ R^S_(≥0)`.

| Shape of `Λ` | Status |
|---|---|
| `C_Λ = {0}` (trapped) | tame wherever something freezes (this node); the sweeping case is open |
| `Λ = Zv`, `v ≥ 0` (positive ray) | tame: 20.44 and torsion decided; 21.74(a) decided when every modulus prime divides `γ`; the neutral-prime case (shared attractor–repeller fixed point) is open |
| `dim C_Λ ≥ 1` and `rank Λ ≥ 2` | contains `G_T` and Conway's `α` when `dim C_Λ = 2`; Collatz-hard in these examples; open in general |

**Conjecture.** Collatz-type hardness requires a genuine positive dilation (an integer slope
product `> 1`) together with a second independent slope direction. Every other shape is tame up to
the sweeping phenomenon.

## Lesson for general BH

**The tameness certificate is a conserved positive level.**
- If positive weights `w` annihilate all slope exponents, every tail is trapped on a finite level
  set. Frozen information then bounds orbits, finite groups are exactly those with finitely many
  slopes, and hardness can only come from dynamics that read every depth.
- The Collatz regime begins exactly where no such level exists and some slope product is an
  integer dilation that can be combined with another direction.
- For hosts, conserved levels are the arithmetic analogue of the length-preserving Turing-machine
  regime: tame at frozen points, and hard only through sweeping heads.

## Referee (bh-ref-q11, 2026-09-19): PASS; item 3 holds, and more generally

**Lemma 1: correct.**
- (ii)⇒(i): the cone `span_Q(Λ) ∩ Q^S_(≥0)` is rational polyhedral, so it has a nonzero rational point, and a multiple of it lies in `Λ`.
- (i)⇔(iii) is Stiemke's alternative, with a rational, hence integral, positive `w`.
- "Product of slopes" must include inverses, since `Λ` is a group.

**Lemma 2: correct** (trivial from `w_q ≥ 1`).

**The examples check.** `w = (1,1,1)` for `⟨3/2, 5/2⟩` and `⟨3/2, 5/3⟩`. `G_T` and Conway's `α` contain `(1,0)`.

**Item 3, the "strong" claim: correct.**
- The key point is that canonical maps carry the **integer** tail exactly. Write `x = ρ + m_n z` with `0 ≤ ρ < m_n` and `z ∈ Z`. A piece `r + km ↦ s + km′` with `m | m_n` sends `x` to `ρ′ + m_(n+λ) z`, where `ρ′ = s + ((ρ−r)/m)m′ ∈ [0, m_(n+λ))`. So there is no carry and no unit twist.
- **Finitely many slopes ⇒ finite.**
  - Let `B` be the finite set of slope exponents of all elements, and `D` the reading depth of the generators. The cumulative shift along any word is the slope exponent of that element at `x`, so it lies in `B`.
  - With `n_q ≥ D + max_(λ∈B)|λ_q|`, the tail is never read. Hence every orbit lies in `{ρ′ + m_(n+λ)z : λ ∈ B}`, of size `≤ Σ_(λ∈B) m_(n+λ)`, **uniformly**.
  - A finitely generated permutation group with uniformly bounded orbits is finite: it lies in `∏ Sym(orbit)` with orbits of size `≤ A`, so it satisfies the laws of `S_A`, and that variety is locally finite.
- **Cone-avoidance is not needed for this direction.** "Finitely many slopes ⇒ finite" holds for every finitely generated `G ≤ CT_P(Z)`.
- Cone-avoidance is needed only for "every point has a frozen tail ⇒ finite": there `Seg(n)` must be finite to bound orbits from a single frozen degree, and compactness supplies finitely many degrees.
- "Finite ⇒ finitely many slopes" is trivial.
- This fits Kohl's theory: an rcwa group is tame iff its moduli are bounded, and tame subgroups of `CT(Z)` are finite, since they preserve `N_0` and are affine on a respected partition. A literature check in Kohl's thesis, for "bounded multipliers ⇒ tame", is advised before any priority wording.

**Items 1, 2 and 4** rest on `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits` and `ct-p-z-mixed-ray-torsion-reduces-to-sweeping-orbits`, which I have not re-refereed.
- The claim that their only use of the ray hypothesis is finiteness of `Seg(n)` agrees with the integer-tail computation above, which is exactly where `Seg(n)` enters (the orbit bound `ρ + m_p z`, `p ∈ Seg(n)`).

**The conjecture** is labelled as such.
