---
rg: 2
id: conway-amusical-permutation-is-the-full-three-shift
kind: claim
title: Conway's amusical permutation lies in CT_{3}(Z) and is conjugate on Z_2 x Z_3 to the two-sided full 3-shift, so CT(Z) contains the full-shift topological full group and every right-angled Artin group; but CT_P(Z) is diagonally rigid and has no one-stack writes in these coordinates
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
  - every-raag-embeds-in-full-shift-topological-full-group
  - full-shift-topological-full-groups-are-torsion-locally-finite
distinct_from:
  full-shift-topological-full-group-embeds-in-2v: that puts the full-shift full group into Brin's 2V, whose two stacks are independent; this puts it into Kohl's arithmetic group CT(Z), whose two stacks are two coprime moduli and cannot be written separately.
  periodic-k-graph-subgroups-with-ray-cocycle-are-finite: that bounds periodic subgroups of CT(Z) whose slopes stay on one ray; this exhibits the rank-two slope regime (slopes 3/2 and 3/4) as the full shift, where that pumping does not apply.
  smart-trace-full-group-embeds-in-brin-thompson-2v: that realizes a minimal subshift inside 2V with a writing Turing machine; this shows that writing is exactly what CT_P(Z) lacks in the coordinates where it contains the shift.
---

**ESTABLISHED** (lane proof below, elementary apart from the cited identification of `CT_P(Z)` with a
full group; not independently reviewed). **No priority claimed.** The map is Conway's amusical
permutation (Conway, "Unpredictable iterations", 1972; see the OEIS entry A006368). A two-sided
itinerary picture is implicit in the 3x+1 conjugacy literature (Lagarias; Bernstein–Lagarias), but
that literature was not read for this node. Kourovka 17.58 (Kohl: does `CT(Z)` have subgroups of
intermediate growth?) is **not** settled here; see "Bearing on 17.58 and 19.46".

## Setting

- `P' = P ∪ {2}` for a set `P` of odd primes, and `Ẑ_P = ∏_{q ∈ P'} Z_q`.
- A *box* is `B(r, m) = r + mẐ_P` with `m` a `P'`-smooth integer and `0 ≤ r < m`.
- The *canonical map* `B(r, m) → B(s, m')` is `x ↦ s + (m'/m)(x − r)`. On `Z` it is the class-wise
  rule `r + tm ↦ s + tm'`.
- `F_P` is the group of homeomorphisms of `Ẑ_P` that are canonical on each piece of a finite box
  partition.
- By `ct-p-z-is-a-one-vertex-k-graph-full-group`, item 3, restriction to the dense invariant subset
  `Z` identifies `F_P` with `CT_P(Z)` for finite `P`.

## Statement

Let `α(n) = 3n/2` for `n` even, `(3n+1)/4` for `n ≡ 1 (mod 4)`, and `(3n−1)/4` for `n ≡ 3 (mod 4)`.

1. **`α ∈ CT_{3}(Z)`.** `α` is the canonical map from `P_0 = 0(2)`, `P_1 = 1(4)`, `P_2 = 3(4)`
   onto `Q_0 = 0(3)`, `Q_1 = 1(3)`, `Q_2 = 2(3)`. Indeed `2t ↦ 3t`, `1+4t ↦ 1+3t` and `3+4t ↦ 2+3t`.
2. **`α` is the full 3-shift.** Define `Φ : Ẑ_{3} = Z_2 × Z_3 → {0,1,2}^Z` by `Φ(x)_n = i` iff
   `α^n(x) ∈ P_i`. Then `Φ` is a homeomorphism with `Φ ∘ α = σ ∘ Φ`.
   - The forward itinerary `Φ(x)_{≥0}` is a function of `x_2` alone.
   - The backward itinerary `Φ(x)_{<0}` is a function of `x_3` alone.
   - Each half determines its coordinate.
3. **Generalization.** Let `p` be an odd prime and `k ≥ 2` with `k ≡ 1 (mod p−1)`. Take a complete
   binary prefix code and a complete `p`-ary prefix code, each with `k` words, viewed as partitions of
   `Ẑ_{p}` into `2`-power boxes `P_i` and `p`-power boxes `Q_i`. The canonical map `α_{P,Q}` sending
   each `P_i` onto `Q_i` lies in `CT_{p}(Z)` and is conjugate to the full `k`-shift, with the same
   proof.
4. **Consequences.** `[[σ_k]] ≤ CT_{p}(Z) ≤ CT(Z)` for every such `k`. By Salo (arXiv:2103.06663, for
   every alphabet; `every-raag-embeds-in-full-shift-topological-full-group`), `CT(Z)` therefore
   contains every right-angled Artin group, for example `Z^2 * Z`, which does not embed in
   `V = CT_∅(Z)` (Bleak–Salazar-Díaz). It also contains `Z/2 ≀ Z` (Salo, same paper).
5. **Diagonal rigidity.** Each `g ∈ F_P` acts on each piece by one map `x ↦ cx + d`, with
   `c ∈ Q_{>0}` a ratio of `P'`-smooth integers and `d ∈ Q`. This is the same affine map in every
   coordinate `Z_q`.
   - Suppose that for some `q ∈ P'` and a nonempty open `W`, `g(x)_q = x_q` for all `x ∈ W`. Then
     `g = id` on `W`.
   - In the coordinates `Φ` of item 2: if an element of `CT_{3}(Z)` leaves the left half-tape
     `Φ(x)_{<0}`, or the right half-tape `Φ(x)_{≥0}`, unchanged on an open set, it is the identity
     there.
   - So `CT_{3}(Z)` contains the shift and its full group, but none of the Brin–Thompson "write on
     one stack" maps (rewrite the cell under the head, keep the other half). This holds at least in
     these coordinates.
6. **Aperiodic elements with odometer fibres.** The element
   `g(n) = 4n+2` (`n` even), `(n+1)/4` (`n ≡ 3 mod 8`), `n−1` (`n ≡ 1, 5, 7 mod 8`)
   lies in `CT_∅(Z) ≅ V`.
   - On `Ẑ_{3}` it has no periodic points.
   - Its only minimal sets are the fibres `{−2/3} × Z_3` and `{1/3} × Z_3`, on which it acts as
     3-adic odometers.
   - So any factor of `(Ẑ_{3}, g)` onto a subshift is finite.

## Proof

**Item 2.** Write `ℓ_0 = 1` and `ℓ_1 = ℓ_2 = 2`, so that `P_i` is a box of modulus `2^{ℓ_i}`.
Canonical maps send sub-boxes to sub-boxes and scale the modulus by the slope.

- **Forward cylinders.** The forward cylinder `C(i_0 … i_{n−1}) = {x : α^j x ∈ P_{i_j}, j < n}` is a
  box of modulus `2^{ℓ_{i_0} + … + ℓ_{i_{n−1}}}`. Induction: if `C' = C(i_1 …)` has modulus `2^L`,
  then `Q_{i_0} ∩ C'` is a box of modulus `3·2^L` (CRT). Its image under the canonical
  `Q_{i_0} → P_{i_0}` (slope `2^{ℓ}/3`) is `C(i_0 …)`, of modulus `2^{L+ℓ}`.
- **Backward cylinders.** Symmetrically, `D(c_1 … c_n) = {x : α^{1−j} x ∈ Q_{c_j}, j ≤ n}` (the
  itinerary positions `−1, …, −n`) is a box of modulus `3^n`. Use `P_{c_1} → Q_{c_1}` (slope
  `3/2^{ℓ}`).
- **Coordinates.** A `2`-power box is a cylinder of `Z_2` times `Z_3`, and a `3`-power box is `Z_2`
  times a cylinder of `Z_3`. So the forward (backward) itinerary depends only on, and determines,
  `x_2` (`x_3`).
- **Φ is a homeomorphism.** Every forward cylinder meets every backward cylinder (CRT). The
  intersections shrink to points, since both moduli go to infinity. So `Φ` is a continuous bijection
  of compact spaces, hence a homeomorphism, and `Φ α = σ Φ` holds by definition.

Item 3 is the same argument with `2`-power and `p`-power boxes.

**Item 4.** Let `h ∈ [[α]]`, so `h = α^{c(x)}` with `c` continuous.
- On a small enough box, `α^c` is one canonical map, since a composite of canonical maps is
  canonical. So `h ∈ F_{3}`.
- `F_{3} = CT_{3}(Z)` on `Z` (cited identification). Restriction to the dense invariant set `Z` is
  faithful.
- Hence `[[σ_3]] ≅ [[α]] ≤ CT_{3}(Z)`. The two cited embeddings then finish the proof.

**Item 5.** Take `x ∈ W` and the piece containing `x`. Some box `B ∋ x` lies in `W` and in that
piece, and there `g(y) = cy + d` in every coordinate.
- Then `c y_q + d = y_q` on the `q`-projection of `B`, which is an open subset of `Z_q`. This forces
  `c = 1` and `d = 0`, so `g = id` on `B`.
- For the tape form, use item 2: the half-tapes determine `x_3` and `x_2` respectively.

**Item 6.**
- **Membership.** The domain pieces `0(2), 3(8), 1(8), 5(8), 7(8)` map canonically onto
  `2(8), 1(2), 0(8), 4(8), 6(8)`, both partitions of `Z`. All moduli are powers of 2, so
  `g ∈ CT_∅(Z)`.
- **The base dynamics.** Every piece is a `2`-power box, so `x ↦ x_2` is a factor map onto the
  action of `g` on `Z_2`.
  - `E = 2Z_2` maps into `2 + 8Z_2 ⊂ E` by `x ↦ 4x+2`, a contraction with fixed point
    `a* = −2/3 ∈ E`.
  - `3 + 8Z_2` maps onto `1 + 2Z_2` by `x ↦ (x+1)/4`, an expansion with fixed point
    `r* = 1/3 ≡ 3 (mod 8)`.
  - The classes `1, 5, 7 (mod 8)` map into `E`.
  - So every point other than `r*` enters `E` and tends to `a*`. The only points staying in
    `3 + 8Z_2` forever form the nested intersection `{r*}`, and backward orbits behave symmetrically.
  - Hence the periodic points in `Z_2` are exactly `a*` and `r*`.
- **The fibres.** On the fibres, `g` acts by `y ↦ 4y+2` and `y ↦ (y+1)/4` on `Z_3`.
  - For `f(y) = ay + b` with `a ≡ 1 (mod 3)` and `b` a 3-adic unit, lifting the exponent gives
    `v_3(f^k(0)) = v_3(b(a^k−1)/(a−1)) = v_3(k)`. So `f` is transitive on every `Z/3^n`, hence minimal
    and conjugate to the odometer.
  - Here `a ∈ {4, 1/4}` and `b ∈ {2, 1/4}`, so both fibre maps are minimal. So `g` has no periodic
    point on `Ẑ_{3}`.
  - A minimal set projects to `{a*}` or `{r*}`, so it is one of the two fibres.
- **No subshift factors.** The image of a minimal set under a factor map onto a minimal subshift is
  the whole subshift. An equicontinuous system has only equicontinuous factors, and an infinite
  subshift is expansive, hence not equicontinuous. `∎`

## Bearing on 17.58 and 19.46

- **Periodic subgroups (19.46).** The full-shift part `[[α]]` of `CT(Z)` is torsion locally finite
  (`full-shift-topological-full-groups-are-torsion-locally-finite`). So an infinite finitely
  generated periodic subgroup of `CT(Z)` must use elements outside every `[[α_{P,Q}]]`.
- **Intermediate growth (17.58).** The route through topological full groups of minimal subshifts
  (Matte Bon's Grigorchuk subshifts, arXiv:1408.0762; Thue–Morse, arXiv:2605.30605), together with
  `aperiodic-full-groups-lift-along-factor-maps`, needs `T ∈ CT(Z)` and a clopen `T`-invariant `U`
  such that `(U,T)` factors onto the subshift.
  - Elements of `[[α]]` never qualify: they have periodic points in every open set.
  - Elements of `V` never qualify. Their minimal sets on `Z_2` are periodic orbits (Brin's
    revealing-pair description, recalled and not re-read). Over such an orbit the return map acts on
    the other coordinates by an affine isometry, so every minimal set on `Ẑ_P` is equicontinuous, as
    in item 6.
  - The known Brin–Thompson realizations (SMART, `smart-trace-full-group-embeds-in-brin-thompson-2v`)
    need a writing head, which item 5 excludes in the coordinates where `CT_{3}(Z)` contains the
    shift.
  - **Open gate:** does some `T ∈ CT_P(Z)` have a clopen invariant set whose minimal subsets are not
    equicontinuous? Equivalently, does Brin's `2V`, or any writing machine, embed in `CT(Z)` in
    coordinates other than these?
- **Constraint on any such `T` (Haar balance, elementary).** Let `a_T(x)` be the slope of `T` at `x`
  and `U` a clopen invariant set. Some `T`-invariant probability `ν` on `U` has
  `Σ_{q ∈ P'} e_q log q = 0`, where `e_q = ∫ v_q(a_T) dν`.
  - Otherwise `∫ log a_T dν` has one sign on the convex set of invariant measures, say `≥ δ > 0`.
    Then `S_N log a_T > 0` on all of `U` for some `N`.
  - But `T^N` maps each piece `W` of a box partition of `U` onto a box of Haar measure
    `μ(W)/a_{T^N}(W)`. Summing gives `μ(U) = μ(T^N U) < μ(U)`.
  - So a uniquely ergodic `T` has `e_2 log 2 + e_3 log 3 + … = 0`. Its exponents either all vanish
    or are not all rational. For `P = {3}`: both vanish, or `e_3/e_2 = −log 2 / log 3`.

**Lesson for general BH.**
- **Two coprime moduli are two stacks.** A Collatz-type map is the baker map, so an arithmetic host
  `CT_P(Z)` (`P ≠ ∅`) contains the whole full-shift full group, which the one-modulus host `V` cannot
  (`Z^2 * Z`).
- **Arithmetic hosts are diagonally rigid.** Every element acts by one affine map in all prime
  coordinates at once. So in the shift coordinates these hosts have the shift but no write head, and
  an extra prime turns the attracting points of `V` into odometer fibres rather than subshifts.
- **Two kinds of Cantor hosts.** The factorizable ones (product k-graphs, `nV`) carry Turing machines
  and minimal non-equicontinuous dynamics. The arithmetic ones (twisted k-graphs, `CT_P`) carry
  shifts and odometers.
- **Consequence for constructions.** A BH construction that needs a writing machine, such as a
  subshift realization or a SMART-type minimal element, must be placed in a factorizable host, or
  must first show that the arithmetic host secretly contains one.
