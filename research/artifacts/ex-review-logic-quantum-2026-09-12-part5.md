# EX review, logic and quantum: part 5. Følner screens and type (A) actors (ex-complexity-amenable), the machine center (complexity-sofic amplifier), liftable masas (ex-hs-masa-lift-*) and torsor port profiles

Lane `ex-verify-logic-quantum`, 2026-09-13 02:00 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.

## 5.0 Verdicts

| item | lane | verdict |
|---|---|---|
| `uniform-folner-gap-switches-have-sigma1-amenable-locus` (+ `-proof`) | complexity-amenable | PASS |
| `recursive-amenable-classes-have-uniform-folner-bounds` (+ `-citation`) | complexity-amenable | PASS.  Cavaleri arXiv:1703.04133v2 Thm 3.1 (p. 7) and Cors 3.4 and 3.6 (p. 9) match verbatim |
| `polycyclic-type-classes-of-fp-groups-are-sigma1-complete` (+ `-proof`) | complexity-amenable | PASS.  The Baumslag--Cannonito--Miller import was not re-read |
| `normalizer-image-of-type-a-actor-is-type-a` (+ `-proof`) | complexity-amenable | PASS: all four conditions of Zaremsky's type (A) are checked |
| `twisted-brin-thompson-wp-equals-actor-orbit-problem` (+ `-proof`) | complexity-amenable | PASS on (a)--(c).  (d) was read at node level |
| `machine-center-vanishes-exactly-on-inf` (+ `-proof`) | complexity-sofic | PASS.  It is stated for `G_0`, following part 1 |
| `machine-center-amplifier-target-not-finitely-presented` (+ `-proof`) | complexity-sofic | PASS.  Cornulier's theorem number was not re-read.  Corrected forward one stale name: `G(P(M_e))` becomes `G_0(P(M_e))` |
| `amenable-type-cycle-kills-liftable-masas` (+ `-proof`) | hs-masa-lift-counter | PASS: all eight steps re-derived |
| `liftable-masa-in-every-model-iff-uniform-hs-kun-partitions` (+ `-proof`) | hs-masa-lift-positive | PASS at node level; artifact not read |
| `vertex-rounding-alone-normalizes-each-theorem-e-model` (+ `-proof`) | hs-masa-lift-positive | PASS on the factorization step; the four premises are established nodes |
| `torsor-cfi-port-profiles-are-cosets` (+ `-proof`) | kac-quantum-compiler | PASS |

## 5.1 Følner screen: PASS

- **(NF2).**
  - A finite set in the 4-regular tree spans at most `|Ω| - 1` edges, so the boundary has at least
    `2|Ω| + 2` edges.
  - `|Ω \ x^-1 Ω| = |Ω \ x Ω|` gives `|Ω \ aΩ| + |Ω \ bΩ| >= |Ω| + 1`.
- **(NF3).**  `|Ω \ xyΩ| <= |Ω \ xΩ| + |Ω \ yΩ|`.
- **(UG1).**
  - Right-coset splitting: `hΩ cap Hc = hΩ_c` for `h in H`.
  - The defects add over cosets and total at most `|Ω|/2`, so some `Ω_c c^-1 ⊆ H ≅ F_2` violates
    (NF2).
- **(UG2).**
  - Pushforward is `l^1`-contracting and commutes with translation.
  - The layer cake gives a level set `L_t` with `|L_t Δ aL_t| + |L_t Δ bL_t| <= |L_t|`, which
    contradicts (NF2).
- **(UG0).**  Amenable members admit `n*`-Følner sets.  Under (UG) non-amenable members do not.
  Cavaleri's Cor 3.4 makes that set r.e., uniformly.
- **Source check.**
  - Thm 3.1: "(i) Γ is amenable; (ii) Γ has subrecursive Følner function; (iii) ... (iv) Γ has
    computable Reiter functions".
  - Cor 3.4: "For every n ∈ N fixed, the set of finitely generated recursive presentations of groups
    admitting n-Følner sets is recursively enumerable".
  - Cor 3.6 is verbatim as quoted in the node.

## 5.2 Recognition cells and actors: PASS

- **Nilpotency induction.**
  - If all weight-`c` generator commutators commute with `X`, they are central.
  - `H/C` then has vanishing weight-`c` commutators, and a central extension adds at most one class.
- **Hardness.**  Every property holds for the trivial group, is inherited by subgroups, and fails for
  `F_2`, so the Adian--Rabin family applies.
- **Type (A) after normalizing.**
  - `ΓQ` is faithful.
  - It is finitely presented, as an extension of f.p. by f.p. (P. Hall).
  - Pair orbits are unions of `Γ`-orbits, so there are finitely many.
  - Point stabilizers are extensions of `Stab_Γ(s)` by a finite-index subgroup of `Λ/Γ`.
- **Twisted Brin--Thompson.**
  - (a): `τ_u x τ_u^-1` moves the support to `u r_i`.  Disjoint coordinates commute, and on the same
    coordinate the commutator is `[x,y]`.
  - (b): brick tracking with `2^(|D| p l)` leaves and `OP` queries; the branch identity test uses
    faithfulness.
  - (c): the transfers.

## 5.3 Machine center: PASS

- **Centrality.**
  - A full configuration word maps to `z_(1,u)` with `u` containing every `A_j`.
  - Formula (13) and pp. 23--24 fix it under every letter: `a_j, a_j', A_j` because `u` contains
    `A_j`, and `ã_j` because `u` contains `A_0`.
  - With `T_0 ≅ T_1`, the commutator is `1`.
- **INF.**  For a simple, universally halting machine every full maximal computation ends at command
  `0`, and the stop relations make the word `1`.
- **FIN.**  The Lemma A word, with `tau = 0`, is `!= 1` and dies in every finite quotient.
- **Target not finitely presented.**
  - `(Z/2) wr_X G` is a retract of `T_e`, by the split coordinate functional and the product
    projection.
  - Cornulier's criterion fails through `|Γ \ G / Γ| = infinity` (SCI5).
  - Finite presentability passes to retracts, since `ker r = << s r(s)^-1 >>`.

## 5.4 Liftable masas: PASS

**Amenable type cycle.**
- **Characters.**  `f = sum_k omega^k e_k` has `V f V^* = omega^-1 f`, so `||[V,f]||_2 = |1 - omega|`.
  For `j_n/L_n -> 0` it lies in `Z(Q)`.
- **Random signs.**  `E ||[V, sum c_A q_A]||_2^2 = sum_A ||[V,q_A]||_2^2`, so a liftable `C <= Q`
  has vanishing summed boundary.
- **One block.**
  - `||x||_1 <= tau(r)^(1/2) ||x||_2 <= sqrt2 tau(q_A)^(1/2) ||[V,q_A]||_2`.
  - `tau(x f) = (1 - omega) tau(q_A f)`.
- **Summation.**  By Cauchy--Schwarz, `sum tau(q_A)|mu_A|^2 <= sqrt2 eps_n/|1-omega|`.
- **Frequency.**  `j_n = max(1, ceil(L_n eps_n^(1/2)))` and `2 sin(πy) >= 4y` give
  `sqrt2 eps_n^(1/2)/4 -> 0`.  So a central element misses `C`.
- **Item 4.**  Intervals of length `ceil((L_n/j_n)^(1/2))` have boundary `<= 2(L_n/l_n + 1)/L_n`,
  and the phase varies by `O((j_n/L_n)^(1/2))` along an interval.

**Positive lane.**
- **Liftable masa iff DEC.**  Steps 4--5 are the Łoś argument of part 3 §3.1.  Step 2 diagonalizes
  the levels along `U`.  BG1--BG4 are an established input.
- **Vertex rounding alone.**
  - The action `alpha` on `σ(Γ)' cap M` is trivial on `Γ`, hence on `<<Γ>>`.
  - Every `e_ij(λ x^v)` is an `SL_d(Z)`-conjugate of `e_ij(λ x_1^m)`, with `v = m w`, `w` primitive
    and `M e_1 = w`.
  - So `G/<<Γ>> = SL_d(Z)`.

## 5.5 Torsor port profiles: PASS

- **Lemma E (≅_t is an equivalence).**
  - Transitivity: `U_(xz) = sum_y v_(xy) (x) w_(yz)` is a colour-preserving magic unitary over
    `A (x) B`.  Tracial states, `R^U` models and finite-dimensional models tensor.
  - Symmetry: pass to `A^op`.
- **Lemma T.**  Port contexts have `T = {τ_i σ_i^-1}` on both sides.
- **Theorem.**  `N''_t` contains `e` and is closed under `δ' δ^-1`.  `N_t = N''_t σ_0`.
- **Boolean ports.**  `(-,+)(+,+)^-1(+,-) = (-,-)`.
