---
rg: 2
id: abelian-normal-closure-fibres-round-linearly-proof
kind: route
title: Homogeneous restriction to an abelian normal A forces every primitive inducing subgroup to contain A; conjugated primitive kernels are then normalized by K
target: abelian-normal-closure-fibres-round-linearly
requires: [primitive-projective-representations-have-a-trace-gap, galois-games-round-through-free-subgroups, galois-unique-game-value-is-transversal-expansion]
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

Derivation (complete). Notation of the artifacts.

**Step 1: primitive inducing subgroups contain `A`.** Let `rho` be irreducible,
`theta` a (linear) constituent of `rho|_A`, and `I` its inertia group, so
`I >= A`. By the Clifford correspondence, `rho = Ind_I^G psi` with `psi`
irreducible and `psi|_A = e theta`. Take `H <= I` minimal such that
`psi = Ind_H^I sigma` for some `sigma`. Then `sigma` is primitive, since
otherwise `psi` would be induced from a smaller subgroup. By Mackey,
`psi|_A = sum over x in A\I/H of Ind_(A cap xHx^-1)^A (sigma^x restricted)`. If
`A' = A cap x H x^-1` were proper in `A`, then for a constituent `lambda` of the
restriction, `Ind_(A')^A lambda` contains all `[A:A'] >= 2` extensions of
`lambda` to the abelian group `A`, and these are distinct characters. That
contradicts `psi|_A = e theta`. So `A <= x H x^-1` for every `x`; in particular
`A <= H`, and `rho = Ind_H^G sigma`.

**Step 2: kernels normalized by `K`.** `ker sigma` is normal in `H`, so
`x (ker sigma) x^-1` is normal in `x H x^-1`, which contains `A` (normal in `G`),
which contains `K`. So `K` normalizes every conjugate of `ker sigma`.

**Step 3: mass.** Theorem 16 of part 4, estimate (16.2), uses only
conjugation invariance and primitivity of `sigma`, together with the required
trace gap. It gives `mu(G \ x (ker sigma) x^-1) <= (1 - lambda_rho)/c(G,m)`. For
M-groups, `sigma` is linear and (11.2) of part 3 gives `1 - cos(2 pi/m)`.

**Step 4: chain.** The symmetric SDP formula of
`galois-unique-game-value-is-transversal-expansion` gives an admissible `phi`.
Step (ii) of irreducible-kernel rounding in
`galois-games-round-through-free-subgroups` needs only `phi = 0` on `K \ {e}`, so
it holds for any `K`: `K cap (intersection over good rho of ker rho) = {e}`,
where good means `w_rho > 0` and `lambda_rho >= 1 - 3 eps`. Since `ker rho` is
the intersection of the conjugates of `ker sigma`, the halving chain of Theorem 12
(part 3) runs with these conjugates. It takes at most `log_q k` steps and gives
`L = L_1 cap ... cap L_t` with `L cap K = {e}` and
`mu(G \ L) <= 3 eps log_q k/c(G,m)`.

**Step 5: value.** Each `L_i` is normalized by `K`, hence so is `L`, and `KL` is
a subgroup. Part 5 of the required claim (permutable rounding) gives
`val >= mu(L)`.

**Model test.** Coordinate fibre `K = <e_0>` in `F_2 wr F_2^n` with coordinate
noise: `A = B`, the good representation is `Ind_B chi_(e_0)`, the primitive
kernel is `{ b_0 = 0 }`, and the output is the permutable hyperplane of
`free-subgroup-rounding-fails-for-non-normal-fibres`. Hypothesis needed: for
`K = <(1 2)>` in `S_N`, the normal closure is not abelian, and this route says
nothing.
