---
rg: 2
id: pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp
kind: claim
title: If β > 1 lies in Z[c] and β^b = c^a for a unit c with property (F), then the Stein group V(Z[c],⟨β⟩,ℓ) is a full contracting RSG on a block recoding of the c-shift, hence finitely presented; for example V(Z[θ],⟨θ+1⟩,ℓ), with θ the plastic number, is a finitely presented simple group although the (θ+1)-shift is not of finite type
distinct_from:
  pisot-unit-slope-stein-groups-are-finitely-presented: that needs the slope β itself to have (F); this needs (F) only for some unit commensurable with β, so it reaches Pisot units whose own greedy expansion fails (F), and even fails finite type.
  negative-base-pisot-stein-groups-are-finitely-presented: that replaces (F) by the negative-base finiteness (F−₀) and uses the square of the coding; this keeps the positive base and uses block recodings of any length, plus slopes that are roots of powers of the coding base.
  stein-derived-groups-need-computable-modules: that is the necessary side of Tanner's question; this widens the sufficient side.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** by `pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp-proof` (lane `bh-partials`; lane proof,
not reviewed; no priority claimed). Inputs: BBMZ Theorem A, Tanner's simplicity theorem, and the AH sequence as stated by
Tanner, the same inputs as `pisot-unit-slope-stein-groups-are-finitely-presented`.

## Statement

Let `c > 1` be an algebraic unit with property (F), and `Γ = Z[c]`. Let `β > 1` with `β ∈ Γ` and `β^b = c^a` for some
integers `a, b ≥ 1`, and let `ℓ ∈ Γ`, `ℓ > 0`.

1. `V(Γ,⟨β⟩,ℓ)` is a full contracting RSG, on the `a`-block recoding of the `c`-shift. So it is finitely presented
   (BBMZ Theorem A), and it and all its subgroups embed in finitely presented simple groups.
2. Suppose moreover `Z[β] = Z[c]`, so that `V` lies in Tanner's standard family; `Q(β) = Q(c)` holds automatically (proof,
   step 0). Let `d` be its degree. If `d ≥ 3`, or `d = 2` and `N(β) = −1`, then `V^ab` is finite, so `D(V)` is a
   finite-index, finitely presented simple group. If `d = 2` and `N(β) = +1`, then `V^ab ↠ Z`; `D(V)` has infinite
   index, and its finite presentation is not decided here.
3. **Special cases.**
   - **Descent** (`b = 1`): every slope subgroup `⟨c^a⟩ ≤ ⟨c⟩` of an (F) unit. Here `Γ = Z[c]` may be strictly larger
     than `Z[c^a]`, so these triples are outside Tanner's standard family `(Z[λ^{±1}], ⟨λ⟩)`.
   - **Ascent** (`a = 1`): slopes `β` with `β^b = c`, `β ∈ Z[c]`.

## The example: slope θ + 1

- Let `θ ≈ 1.3247` be the plastic number, `θ³ = θ + 1`; it has (F) (Akiyama, read at source; see
  `pisot-stein-groups-are-contracting-rsgs`).
- Put `β = θ³ = θ + 1 ≈ 2.3247`, a cubic Pisot unit with minimal polynomial `x³ − 3x² + 2x − 1`, and `Z[β] = Z[θ]`.
- **β has no (F).** `d_β(1) = 2 0 1 1 1 ⋯` is infinite:
  - `β·1 = θ + 1` gives digit 2, remainder `θ − 1`;
  - `β(θ − 1) = θ² − 1` gives digit 0;
  - `β(θ² − 1) = θ³ + θ² − θ − 1 = θ²` gives digit 1, remainder `θ² − 1` again.

  So the β-shift is not of finite type, and neither `pisot-unit-slope-stein-groups-are-finitely-presented` nor the
  coding of `pisot-stein-groups-are-contracting-rsgs` applies to it.
- **Item 1 still applies** with `c = θ`, `a = 3`, `b = 1`: `V(Z[β],⟨β⟩,ℓ)` is finitely presented.
- **V is perfect.**
  - `|H_0| = |N(1 − β)| = |N(−θ)| = 1`.
  - `H_1 = coker(1 − Λ²A)` has order `|N(β − 1)/N(β)| = |N(θ)| = 1`.
  - So `V^ab = 0`, matching Tanner's formula `Z/(a_1 + a_2)` for `λ = β^{-1}`, the root of `t³ − 2t² + 3t − 1`.
- So `V(Z[θ],⟨θ+1⟩,ℓ) = D(V)` is itself a finitely presented infinite simple group, for every `ℓ`.

## Where Tanner's question stands (cyclic Λ)

- **Sufficient conditions, now:**
  - the slope is commensurable, inside the same ring, with an (F) unit (this node);
  - the slope is an (F−₀) unit `> 2` (`negative-base-pisot-stein-groups-are-finitely-presented`). Its powers are covered
    too, by item 1's block recoding, whenever that node's square coding graph is aperiodic; this was not checked;
  - every quadratic unit gives a finitely presented V.
- **Open:**
  - Pisot units that are neither (F−₀) nor commensurable, inside their own ring, with an (F) unit;
  - non-Pisot algebraic slopes, for which no contracting coding is known;
  - non-unit slopes such as 2/3;
  - `D(V)` for quadratic slopes of norm `+1`, which is finite presentation of the kernel of a character `V ↠ Z`, a
    `Σ²` question.
- **Necessary conditions:** computable ratios (`stein-derived-groups-need-computable-modules`), and non-finite
  presentation for hard Liouville slopes (`hard-slope-thompson-groups-have-no-piecewise-projective-hosts`).

## Lesson for general BH

- **Finite presentation sees the numeration, not the slope's greedy shift.**
- **What the obstruction is.** It is not the symbolic complexity of the β-shift: here that shift is not even of finite
  type. It is the existence of *one* finite numeration with ratios in Λ whose finite expansions are exactly `Γ ∩ [0,1)`.
- **Block recoding transfers the numeration.** It moves such a numeration along commensurability of slopes, and it
  keeps both the boundary set and the finite nucleus.
- **What this means for hosts.** An RSG host problem is a finiteness problem for the pair (breakpoint module, slope
  group). The master route's other finiteness gates (finite type ⇒ finite presentation, P2) have the same shape.
