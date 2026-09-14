---
rg: 2
id: laurent-sl-n-representations-have-sl2-invariant-vectors
kind: claim
title: Every finite-dimensional unitary representation of SL_n(F_q[t^±1]) is congruence, and for n ≥ 4 it fixes a vector under the block SL_2, so the Laurent lattice is not purely matricial field
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that is the published Magee-de la Salle theorem for SL_4(Z), whose proof uses superrigidity and the congruence subgroup property; this is the positive-characteristic Laurent lattice, where torsion root subgroups and Bass-Milnor-Serre give congruence directly.
  sl4-over-finite-chain-rings-has-sl2-invariant-vectors: that is the statement for SL_4 over finite principal ideal rings; this reduces every finite-dimensional representation of the infinite Laurent lattice to it.
  minimally-almost-periodic-groups-are-not-pmf: that excludes PMF for groups with no finite-dimensional representations; this group is residually finite, and every one of its finite-dimensional representations carries an invariant vector.
artifacts:
  - research/artifacts/sk-matricial-stability-laurent-sl4-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `q` be a prime power, `A = F_q[t,t^{-1}]` and `n ≥ 3`. Let `ρ` be a
finite-dimensional unitary representation of `SL_n(A)`.

1. **Congruence.** There is a nonzero ideal `J ⊆ A` such that `ρ` factors through `SL_n(A) → SL_n(A/J)`. In
   particular `ρ` has finite image.
2. **Invariant vectors.** If `n ≥ 4` and `dim ρ ≥ 1`, then `ρ` has a nonzero vector fixed by the upper-left `SL_2(A)`.
3. **Not PMF.** Let `S, T` be free generators of a free subgroup of `SL_2(F_q[t])`, in the upper-left block, and
   `z = S + S^{-1} + T + T^{-1}`. For `n ≥ 4`, `‖ρ(z)‖ = 4` for every such `ρ ≠ 0`, while
   `‖λ_{SL_n(A)}(z)‖ = 2√3`. So no sequence of finite-dimensional unitary representations converges strongly to the
   regular representation, for `SL_n(A)` and for every group containing `SL_4(A)`.

**What it replaces.** `research/artifacts/sk-cstar-mf-firewall-2026-09-13.md` §4 recorded item 3 as a sketch through
Margulis superrigidity in positive characteristic plus Bass–Milnor–Serre, neither read. This proof uses no
superrigidity. Its one import is Bass–Milnor–Serre Corollary 4.3, read from the scan
(`bms-congruence-kernel-trivial-not-totally-imaginary`).

**Scope.** Steps 1–4 of the route use only that `A` has positive characteristic, is a Dedekind ring of arithmetic
type that is not totally imaginary, and is a principal ideal domain with finite quotients. The principal-ideal step can
be replaced by the Chinese remainder theorem, so items 1–2 should hold for every ring of `S`-integers of a global
function field. That extension is not written out here.

Proof: route `laurent-sl-n-representations-have-sl2-invariant-vectors-proof`.
