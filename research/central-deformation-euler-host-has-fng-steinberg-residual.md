---
rg: 2
id: central-deformation-euler-host-has-fng-steinberg-residual
kind: claim
title: The central-deformation Euler host T_p, in which the lamps are non-units and only a central element p becomes 1 on the corner, has a finitely normally generated Steinberg finite residual for some N
distinct_from:
  euler-triangular-steinberg-rf-residual-is-fng: that is the question for T_l, whose lamps π_k are commuting units and carry the symbols {π_0, π_q}; here the lamps are not units, so those symbols are not defined in the host.
  one-sided-inverses-cannot-repair-the-steinberg-residual: that shows one-sided inverses reduce to T_l; here p − 1 is not in the finite residual ideal, so that reduction does not apply.
  euler-ring-steinberg-rf-residual-is-fng: that concerns the quotient D = B/(p − 1); this host maps onto T_l but is not a retract of anything known to carry the symbols.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**OPEN (2026-09-18, lane gq-k2-q).** For some prime `l` and some `N >= 5`, the finite residual of `St_N(T_p)` is
finitely normally generated. With the verified facts below, this would give a finitely presented residually finite
group `Γ_N(T_p) = St_N(T_p)/St_N(T_p)_rf` containing `Z_(l)`, provided `T_p` is residually finite (open, item 5).

## The host

- `B = Z<u, b, x, x^(-1)>` with relations
  - `x x^(-1) = x^(-1) x = 1`;
  - `x u x^(-1) = u + l`;
  - `b u = u b`;
  - `x p x^(-1) = p`, where `p = b(u + 1)`.
- `M = B/(Bu + B(p − 1))`, with generator `m_0`.
- `T_p = [[B, M],[0, Z]]`.

## Verified (lane proof, elementary)

1. **`p` is central in `B`.**
   - `b` commutes with `u`, so `π_0 = u + 1` commutes with `b` and with `p`.
   - `x` commutes with `p` by the last relation.
   - `pb = bπ_0 b = b bπ_0 = bp`.
2. **`B/(p − 1) ≅ D`**, the Euler ring of `resolvent-ring-has-path-normal-form`.
   - Modulo `p − 1`, `b π_0 = π_0 b = 1`, so `b = π_0^(-1)`, and the last relation becomes trivial.
   - The inverses `x^k π_0^(-1) x^(-k) = π_k^(-1)` commute, being inverses of the commuting `π_k = u + 1 + kl`.
   - So the quotient is `Z[u][π_k^(-1)][x^(±1); σ] = D`.
   - Since `p` is central, `B(p − 1)` is two-sided, and `M = D/Du`, which is the Euler base `Z_(l)[y^(±1)]` of
     `euler-triangular-ring-is-fp-rf`.
3. **`T_p` is finitely presented and `Z_(l) ⊆ M`.**
   - `B` has finitely many relations, and `M` is a cyclic `B`-module with two relations.
   - Directly, with `b_k = x^k b x^(-k)`: `b_k π_k = x^k p x^(-k) = p`, and `π_k m_0 = (1+kl) m_0`. So
     `(1+kl) b_k m_0 = b_k π_k m_0 = p m_0 = m_0`.
   - `M` is torsion-free, so `m_0` generates a copy of `Z_(l)`. It embeds in `St_N(T_p)` through `m ↦ x_12(m)`, since its image `e_12(m)` in `E_N(T_p)` is injective.
4. **The lamps are not units of `B`.**
   - `u ↦ u`, `b ↦ t/π_0`, `x ↦ x` defines `B -> A_p[x^(±1); σ]`. Here `A_p = Z[u, t][t/π_k : k ∈ Z] ⊂ Q(u)[t]`,
     with `σ(u) = u + l` and `σ(t) = t`. All relations hold, with `p ↦ t`.
   - `A_p` is graded by `t`-degree, with degree-0 part `Z[u]`, so `A_p^x = {±1}`. The units of the skew Laurent
     ring over the domain `A_p` are `±x^k`.
   - So `π_0 ↦ u + 1` is not a unit, and neither is any `π_k`. In particular the Steinberg symbols
     `{π_0, π_q}` of `euler-ring-rational-symbols-are-infinitely-generated` are not defined over `B`. They exist
     only in the quotient `T_p/(p − 1) = T_l`.
5. **`p − 1` is not in the finite residual ideal.**
   - `u, b ↦ 0` and `x ↦ 1` define `B -> F_l`, with `p ↦ 0`. Together with `M -> 0`, this gives a finite quotient
     of `T_p` in which `p ≠ 1`.
   - So `one-sided-inverses-cannot-repair-the-steinberg-residual` does not collapse `T_p` to `T_l`.

## Open checks

- **(C1) Residual finiteness of `B` and `T_p`.** The lamps `b_k` need not commute in `B`. Both `π_j` and `π_k`
  kill `[b_j, b_k]` on the left, because `π_j b_j = p` is central. If some `π_j` is a zero-divisor, `B` is larger
  than its image in `A_p[x^(±1); σ]`.
- **(C2) `K_2`.** `K_2(B) ⊕ K_2(Z)` is a direct summand of `K_2(T_p)`, by the retractions of
  `euler-ring-rational-symbols-are-infinitely-generated`, Part 3. Equality is the triangular theorem of
  Berrick–Keating, not read at source.
  - The question is whether `K_2(N, T_p)` contains an infinitely generated family dying in every finite quotient.
  - The `D`-symbols are absent. The residue invariants `I_p` must be re-derived, since the lines `π_k = 0` are not
    divisors of `Spec A_p`.
- **(C3) Finite quotients.** In a finite quotient, the Fitting decomposition of the central `p` splits the ring
  into a part where `p` is a unit and `π_k` is invertible (Euler type), and a part where `p` is nilpotent. The images
  of `K_2(N, T_p)` in the Euler-type parts are where a `c_q`-type obstruction could reappear.
