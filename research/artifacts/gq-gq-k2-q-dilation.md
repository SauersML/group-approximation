# The dilation-letter loophole (lane gq-k2-q, 2026-09-18)

Coordinator's question: can finitely many dilation letters `N ↦ pN + r` (finitely many primes) plus a resolvent
vacuum make `[1]` divisible by every `n`, with no two-register comparison and no Π_1/Π_2 simplicity trap?

**Verdict: no in the nonsingular case (proved), no in every singular example tested.** Node
`dilation-letters-cannot-divide-the-unit-class`.

## 1. The shape

- One register `N >= 0` per type.
- Letters `x` with `σ_x(N) = p_x N + r_x`. Under the future semantics `N(xξ) = p_x N(ξ) + r_x`, so from a level-`k`
  state `x` leads to the level `(k − r_x)/p_x`, when that is an integer.
- Optional loops, shifts, upward letters and resets.
- A resolvent vacuum for `Q`.
- Availability eventually constant, which is automatic for idempotents of the coefficient ring.

## 2. Why the resolvent cannot supply the missing primes

- `K_0(B⁺)` is the group of indicator classes `LC(N ∪ ∞, Z)` per type, whatever resolvents are adjoined (excision
  plus `K_0` of a localized polynomial ring). The resolvents live in `K_1`.
- Every prime dividing `[1]` must therefore come from the combinatorics of `1 − [X]` on indicator classes.

## 3. Why dilations do not supply them either

- Dilations send level `k` to level about `k/p`, strictly below `k`.
- A division `m · V_new = known` needs a new class that is the target of a family, at one stage, whose determinant
  grows. With one register per type, the only letters reaching the top level are shifts, whose eventual
  coefficient matrix `M_top` is constant.
- If `det M_top ≠ 0`, every harmonic functional has denominators dividing powers of `det M_top` (the proof route).
  A bounded-denominator functional nonzero on `[1]` then limits divisibility to finitely many primes.
- The `p^n` multiplicities of iterated dilations point the wrong way: they write a high class as a sum of low
  classes.

## 4. Examples

| design | result |
|---|---|
| all residues of one base `p`, no loop | `X = pX`: `[1]` is `(p−1)`-torsion (the Cuntz `Q_N` / Leavitt phenomenon) |
| one loop and all residues of base 2 | `V_(⌊k/2⌋) = 0` for all `k`: every point class vanishes, and `X = 3X` |
| one loop and all residues of bases 2 and 3 (singular) | harmonic `h` gives `h(⌊k/2⌋) + h(⌊k/3⌋) = 0`; induction with `k = 2j` gives `h ≡ 0` on points; `X = 6X` gives `5X = 0`, so `[1]` is torsion |
| loops `a ≠ 1`, downward letters only | nonsingular, since `M_top = 1 − a ≠ 0`, and the node applies |

## 5. Simplicity and register units

- **Simplicity.** A one-register dilation design has no comparison between two registers, so the capacity-type
  trap does not arise. Cuntz's `Q_N` suggests such rings can be simple. The question is moot, because `K_0`
  already fails.
- **Register units.** `σ(N + c) = p(N + (r+c)/p)` forces resolvents at every `c ∈ Z[1/p]`. The tail-unit lattice
  of `resolvent-register-units-give-rational-symbols` is then indexed by `Z[1/p]`. This was not computed.

## 6. What remains for the target

All register designs are now bracketed:
- one register (shifts, resets, dilations): bounded divisibility;
- two registers: comparison trap;
- `sl_2`: the same comparison in disguise.

The open shapes are:
- the singular case `det M_top = 0` in general;
- hosts not of register type.
