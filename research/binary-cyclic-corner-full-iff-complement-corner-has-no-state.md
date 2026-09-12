---
rg: 2
id: binary-cyclic-corner-full-iff-complement-corner-has-no-state
kind: claim
title: The binary cyclic corner is full exactly when its complement corner carries no K_0 state
distinct_from:
  twisted-leavitt-corner-fullness-equals-absence-of-k0-states: that is Theorem E on a twisted visible factor with m dividing q - 1, where the augmentation vanishes on the factor; this is the untwisted binary corner over F_2, where the augmentation state never vanishes, handled through the complement corner and a second halving homomorphism.
  binary-cyclic-averaging-idempotent-is-full-on-leavitt-units: that is the open fullness target; this is an established equivalence turning it into the absence of states on the complement corner (1 - e) F_2[R^x] (1 - e).
artifacts:
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-binary-upg`; verification requested from `w4-vf-linear-b`) by
`binary-cyclic-corner-state-criterion-proof`.

Let `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, with the ternary family `s_1 = s0`, `s_2 = s1 s0`,
`s_3 = s1 s1`. Let `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, `e = 1 + [g] + [g²]`, `f = 1 - e` and
`T = f A f`. The following are equivalent.
1. `c e b = 1` is solvable in `A` (`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`).
2. `A` is isomorphic to a direct summand of `eA`.
3. `[f] <= 0` in `K_0(A)`.
4. Every state on `(K_0(A), [1])` gives `[e]` the value `1`.
5. `(K_0(T), [T])` admits no state.
6. `T` fails the rank condition.

**Proof ingredients** (artifact Sections 1–2).
- **Two halving homomorphisms:** with `D(h) = Σ s_i h t_i`, both `ψ(x) = e D(x)` and `ψ'(x) = f D(x)`
  are unital ring homomorphisms, into `eAe` and into `T`.
- **Tower relations:** `[fA] = 3[(e - e_(C_3²))A]`, and `ψ` shifts the classes `[e_(C_3^k)]`, so
  `[eA] >= N[(E_k - E_(k+1))A]` for `N <= (3^k - 1)/2`.
- **5 => 1:** absorption `N v + v <= N v` in the complement ideal is pushed down the tower until `[eA]`
  absorbs `[fA]`.
- **4 => 5:** every state of `T` pulls back along `ψ'` to a state of `A` with `[f] -> 2/3`.

**Scope.** The same holds for `F_2[H]`, for every subgroup `H <= G` that contains `g` and the nine-cylinder
permutation units and satisfies `D(H) ⊆ H`.

**Why it matters.** The augmentation state of `A` never obstructs the corner. This criterion isolates the
only possible obstruction, a state on the augmentation-free corner `T`. Together with
`binary-complement-corner-rank-functions-pull-back-to-units`, it reduces the binary counterexample to the
Sylvester form of the two-root gate plus one ring-theoretic step (U1) for `T`.

## Attempts

Established, not open. Proof in artifact Section 2.
