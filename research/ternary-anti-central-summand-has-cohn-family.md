---
rg: 2
id: ternary-anti-central-summand-has-cohn-family
kind: claim
title: The anti-central summand of the ternary Leavitt group algebra contains a unital two-pair Cohn family
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the corner equation c e_- b = eps_- for the swap-averaging idempotent; this is the idempotent-free equation tau_i sigma_j = delta_ij in the whole summand, equivalent to it through the diagonal endomorphism.
  ternary-twisted-algebra-has-swap-separated-one-sided-pair: that is one one-sided pair c a = 1 whose partner kills the swap translate, c [w] a = 0; this is two orthogonal one-sided pairs with no reference to the swap, a free summand of rank two inside rank one.
  ternary-leavitt-unit-group-nonsurjunctive: that is the root asking for a strict automaton on the ternary unit group; this is an algebraic target sufficient for it through the swap corner.
artifacts:
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

**OPEN.** Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S_- = F_3[G] / (1 + [z])` with unit `1_-`.
Exhibit `sigma_1, sigma_2, tau_1, tau_2` in `S_-` with

    tau_i sigma_j = delta_ij 1_-.

**Equivalent forms**, all proved in Theorem 2.1 of the artifact:
- `S_-^2` is isomorphic to a direct summand of `S_-`;
- some `sigma_j`, `tau_i` have Gram matrix `[tau_i sigma_j]` invertible in `M_2(S_-)`;
- `ternary-anti-invariant-swap-corner-is-full`, through the routes
  `anti-central-cohn-family-gives-swap-corner-fullness` and
  `swap-corner-fullness-gives-anti-central-cohn-family`.

**Necessary conditions.**
- The support of a witness, together with `z`, generates a group that is not `F_3`-linear sofic
  (Proposition 2.4).
- `F_3`-linear soficity of `G` would refute this claim (`linear-sofic-group-algebra-is-stably-finite`).

**What does not obstruct it.** No augmentation exists on `S_-`, so the no-Leavitt-family argument for
group algebras over a field does not apply here (Remark 2.3).

**What the trace says.** The canonical trace has `tau(1_-) = 2`. It forbids unital binary Leavitt
families in `S_-` and fixes `tau(p) = 1` for the defect `p` of any Cohn family
(`anti-central-ternary-summand-has-no-binary-leavitt-family`). A quaternary Leavitt family is
trace-compatible and sufficient (`ternary-anti-central-summand-has-quaternary-leavitt-family`).

## Attempts

- *Lifts of the Leavitt generators.* `pi_-` maps `S_-` onto `R`, where `(t_i, s_j)` is a Cohn family.
  For lifts `sigma_j` of `s_j` and `tau_i` of `t_i`, the Gram matrix lies in `I + M_2(K_-)`, with
  `K_- = ker pi_-`.
  - Invertibility of that Gram matrix is exactly the target, and a nilpotent defect is enough.
  - `K_-` contains nonzero idempotents (lane gk-l3-kernel), so invertibility is not automatic.
  - Where it dies today: no lift with a computed invertible Gram matrix is known.
- *Honest monomial lifts* (Section 3 of the artifact).
  - In characteristic three every cylinder projection `p` lifts to the idempotent `2(1 - [1 + p])`,
    and every disjoint-cylinder partial isometry lifts to idempotent . transposition . idempotent.
  - A lift of `s_0` always contains a comparable piece `S[0^(k+1)] T[0^k]`, which is itself a
    conjugate of `s_0`. So honest monomial pieces never assemble the isometry.
  - Lane gk-l3-free reports that an invariant measure excludes such monomial compressions inside the
    signed Thompson group. Witnesses must use mod-3 overlaps or non-monomial units.
- *The natural lift of `(s0, t0)`, computed exactly* (Lemma 3.3 of the artifact).
  - With Thompson units `g, h`, the lifts `a = [g] P_0 + [h] P_1` and `c = [g^-1] P_00 + [h] P_01`
    give `c a = 1_- + [g^-1 h] P_00 P_1 + [h g] P_10 P_0`. Every defect term is a unit times a product
    of honest lifts of disjoint cylinders, a nonzero kernel idempotent.
  - Orthogonal character lifts kill the cross terms but miss the kernel mass of the multi-minus
    characters.
  - So monomial lifts pay in cross terms or in mass. That is the finite shadow of gk-l3-free's
    measure obstruction.
  - Where it dies: no monomial correction removes both.
- *Idea, not yet tested: extension fields and roots of unity.*
  - Corner solutions ascend to `F_(3^k)` (lane gk-lp-hosts). The honest-lift XOR law uses only
    characteristic three, so the mass dichotomy for cylinder partitions persists there.
  - Over `F_9` the order-four Hadamard unit (`h_H^2 = z`) has spectral idempotents
    `(1 + zeta^-1 x + zeta^-2 x^2 + zeta^-3 x^3)/4`. These are non-monomial honest idempotents
    outside any cylinder partition, which is the kind of escape the dichotomy leaves open.
  - Tested (lane w3-corner-cohn-b, `f9-hadamard-spectral-cohn-attempt-2026-09-12.md`).
    - **Coefficients.** F_9 families are equivalent to F_3 families: `Phi = J o (rho (x) id)` is unital
      (`f9-cohn-family-descends-to-anti-central-summand`).
    - **Spectral halves.** The depth-one spectral halves `2(1 +/- i[h])` are conjugate through a
      constant unit, and their fullness gives this claim (`hadamard-spectral-fullness-gives-f9-cohn-family`).
    - **Collapse.** Each gives a 2x2 `F_3` design on supports closed under right multiplication by
      `h`, not conversely, and there is no one-element-per-half lift. No witness.
- *Mixed-depth monomial lifts, exact defect* (lane w3-corner-cohn-a,
  `natural-leavitt-pair-lifts-have-partial-symmetry-defect`).
  - Take any Thompson units `g_0, g_1` extending `s_0` on the first-letter cylinders, and the lifts
    `sigma = [g_0]P_0 + [g_1]P_1`, `tau = [g_0^-1]P_00 + [g_1^-1]P_01`. Then `tau sigma = 1 + D`, where
    `D` is a partial symmetry on one nonzero kernel idempotent `F`: `D^2 = F`, `DF = FD = D`.
  - A corrected lift `tau''` of `t_0` gives `tau'' sigma = 1 - e'` with `e' = 2(F - D)` a nonzero
    kernel idempotent. So the lift of `s_0` is left invertible exactly modulo `e'`, for every choice of
    mixed-depth units. The choice changes the sets, never the defect type.
  - No functorial repair: `no-equivariant-lattice-lift-of-cylinder-idempotents` excludes any
    `V`-equivariant Dirac-compatible Boolean lift of the cylinder idempotents.
  - Where it dies: a witness needs some `x` with `x sigma = e'`. `{0,1}`-valued monomial corrections are
    Haar-excluded. What is left is coefficients `2` on overlaps, units outside `E x| V`, or a skeleton for
    the lifts of `s_1` making the whole `2 x 2` Gram defect a single partial symmetry (not yet computed).
  - **Resolved, dead** (lane w4-cohn-gram, `mixed-depth-leavitt-lift-is-a-left-zero-divisor`).
    - `sigma e' = 0` and `e' tau = 0`. So no `x` with `x sigma = e'` exists.
    - No `2 x 2` Gram matrix containing `sigma` or `tau` is invertible, whatever the lifts of `s_1` are.
    - The defect is annihilated, not removable.
- *Zero-divisor filters for entries in the crossed product* (lane w4-cohn-gram,
  `crossed-product-zero-divisor-filters-2026-09-12.md`).
  - **Non-zero-divisors.** Every Cohn entry must be a non-zero-divisor on the appropriate side, also after
    multiplication by units. Inside `B`, zero divisors are read on fibre operators over `F_3[V]`
    (`crossed-product-zero-divisors-are-detected-on-fibres`).
  - **Monomial and peeling.** An entry in `B` with column weight or image multiplicity at most one is a
    unit or a two-sided zero divisor (`monomial-crossed-product-elements-are-units-or-zero-divisors`).
    More generally, an entry whose column peeling stops or terminates in finitely many rounds is dead
    (`triangular-crossed-product-elements-are-units-or-zero-divisors`). This includes three-piece
    honest lifts of `s_0`.
  - **Expansion.** A family inside `B` needs `|N_(sigma_1)(J) ∪ N_(sigma_2)(J)| >= 2|J|` on every finite set
    of every orbit, and a non-hyperfinite coefficient relation
    (`hyperfinite-coefficient-graphing-excludes-corner-witnesses`).
  - **Where it dies.** Untouched: entries in `B` whose peeling keeps a positive-measure core with at least
    two live points per column, and units outside `E x| V` used additively.
