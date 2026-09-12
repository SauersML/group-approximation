---
rg: 2
id: heisenberg-centre-pairing-constrains-two-root-defect
kind: claim
title: The Heisenberg centre pairing of an EL_3 rank model forces the two-root defect to vanish
distinct_from:
  el3-two-root-violation-splits-over-leavitt-branches: that splits the defect over the Leavitt branches and gives an upper bound; this uses the commutator pairing valued in the nilpotent centre and a bounded-rank versus onto tension.
  rank-four-isometry-relations-give-corner-cuntz-family: that uses the fourth EL_4 index to assemble a corner Leavitt family; this stays inside EL_3 and uses only the centre of its unipotent radical.
artifacts:
  - research/artifacts/rank-four-associativity-gate-plans-2026-09-12.md
---

**OPEN.** Let `R = L_K(1,2)`, `K` finite of characteristic `p`, and `sigma : EL_3(R) -> M^x` a rank
model. The unipotent radical `U = <x_12, x_23, x_13>` is two-step nilpotent with centre
`Z = x_13(R)`, and the commutator pairing `U/Z x U/Z -> Z`, `(x_12(a), x_23(b)) |-> x_13(ab)`,
becomes an `F_p`-bilinear pairing `beta : R x R -> n_13(R)`, `beta(a,b) = n_13(ab)`. Then the
two-root defect `D = N_23 N_12` is zero.

## Mechanism

`sigma(U)` is nilpotent, `sigma(Z)` is central in it, and `n_13(R)` is an abelian, additively
square-zero subgroup of bounded rank (`rk(n_13(a)) <= rk(N_13)`, conjugation-invariant across
positions). By the defect factorization `el3-two-root-violation-splits-over-leavitt-branches`,
`n_13(ab) - n_12(a) n_23(b)` is a unit conjugate of `n_23(b) n_12(a)`, so `beta` is "balanced" exactly
when `D = 0`. Because `R.R = R` -- indeed `1 = s_0 t_0 + s_1 t_1` is a sum of two products -- `beta`
is onto `R` in the sense that `n_13(R)` is spanned by pairing values. The plan is to show a
bounded-rank bilinear pairing onto `R`, with `R ~= R^2`, produces an infinite orthogonal chain of
rank pieces unless the defect vanishes.

## Attempts

- **Elementary and EL_3-internal.** Independent of the fourth-index assembly
  `rank-four-isometry-relations-give-corner-cuntz-family`; uses only the centre of the Heisenberg
  radical, so it needs no `EL_4` room.
- **First lemma.** `beta` is `F_p`-bilinear and conjugation-invariant, and its symmetric defect is
  `rk(D)`. To be shown: iterate `R ~= R^2` (`s_i, t_i`) to split `beta` into two half-pairings of
  equal rank plus a cross term (the branch split of `el3-two-root-violation-splits-over-leavitt-branches`),
  and read the iteration as a strictly increasing chain of orthogonal images in the bounded-rank
  group `n_13(R)`.
- **Where it stops.** The bounded-rank-versus-onto tension is not yet a contradiction: the branch
  split only bounds `rk(D) <= 2 rk(D_branch) + rk(cross)`, and the cross term is not yet controlled.
  Ranked below Plan 1 for this reason.
- **Dies as a mechanism (w4-heisenberg, 2026-09-12).** Every input lives in `UT_3(R)`, or in
  `UT_3(R) ⋊ <diag(w,w,w)>`. Both groups are locally finite, and their direct-limit regular
  representation is a genuine rank model that realizes the free profile on every finite subgroup at
  once. It satisfies every input:
  - the Steinberg relations with any coefficients, Leavitt ones jointly;
  - centrality of `n_13(R)` and the pairing;
  - `rk n_13(c) = 1/2`;
  - rank equalities across positions;
  - the branch split and the swap.

  In that model `rk(N_23 N_12) = 3/8`. The hoped-for chain does not appear: the `2^k` depth-`k`
  branch products each have rank `3/8`, so they are not independent
  (`unitriangular-data-cannot-assemble-corner-leavitt-families`, artifact
  `research/artifacts/heisenberg-and-rank-four-positive-root-firewall-2026-09-12.md`). The claim's
  conclusion is untouched; it is the gate. A proof must use `sigma` as an operator outside the
  unitriangular group, jointly on a nonsofic subgroup.
- **Unitriangular calibration: dies as written (w4-r4-adversary, c6697aa47b).**
  - **The model.** The homomorphism `U_3(R) -> F_p^2 -> GL(F_p[C_p^2])`, through the superdiagonal
    entries, has `rk(N_23 N_12) = (p-1)^2/p^2` and `beta = 0`. It satisfies every relation of
    `U_3(R)`, and `R ~= R^2` is a property of `R` alone.
  - **What fails.** No contradiction "unless `D = 0`" follows from `U_3` relations, bounded rank of
    `n_13(R)`, and `R.R = R` (`unipotent-frame-relations-cannot-assemble-corner-cuntz-family`).
  - **Rank symmetry does not help.** The regular sofic model of the nilpotent group `U_3(R)` has
    position-symmetric ranks `1 - 1/p` and nonzero centre data, and in characteristic two
    `rk(D) = 3/8` (`sofic-subgroups-carry-rank-models-violating-two-root-identity`). So conjugation
    invariance read as rank equalities across positions does not help.
  - **What a proof must use.** The first lemma must use operator conjugation by Weyl or opposite root
    elements, and those generate a copy of `R^x` (artifact
    `research/artifacts/rank-four-plan-adversarial-audit-2026-09-12.md`, Section 3).
