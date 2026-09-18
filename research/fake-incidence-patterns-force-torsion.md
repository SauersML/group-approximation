---
rg: 2
id: fake-incidence-patterns-force-torsion
kind: claim
title: If a minimal-window Shannon LP is below one in any group, the configuration's incidence pattern occurs in no torsion-free group
distinct_from:
  torsion-free-windows-have-minimal-shannon-certificates: that asks for LP >= 1 on configurations of torsion-free groups; this asks, for fakes in arbitrary groups including finite ones, that the pattern of coincidences forces torsion. This implies that claim, but it can be refuted by a computation inside a finite group.
  shannon-window-fakes-transfer-to-canonical-hosts: that proves the transfer lemma and checks this statement on the 151 known fakes and 1274 enumerated patterns; this is the general statement for every configuration.
  finite-torsion-free-pattern-realizable-finitely-presented: that realizes finite equation-and-inequation patterns in finitely presented torsion-free groups; this conjectures that a specific kind of pattern, the coincidences of an LP fake, admits no torsion-free realization at all.
artifacts:
  - research/artifacts/shannon-fakes-canonical-host-transfer-2026-09-17.md
  - experiments/shannon-canonical-hosts-2026-09-17/base_rate.txt
  - experiments/shannon-canonical-hosts-2026-09-17/free_host_lp.txt
  - experiments/shannon-canonical-hosts-2026-09-17/recheck_all.txt
---
**OPEN.**

**Setup.** `LP_G(E,F)` is the minimal-window Shannon LP of
`research/artifacts/shannon-window-certificates-2026-09-17.md`, Section 2. The incidence pattern `P` of `(E,F)`
consists of the index sets `E` and `F`, the coincidences `fe = f'e'` and the products `fe = 1`. A realization of
`P` is a group `K` with maps `E -> K` and `F -> K` whose products have exactly these coincidences and exactly
these products equal to `1`.

**Claim.** Let `G` be any group and `(E,F)` a configuration in `G` with `LP_G(E,F) < 1`. Then no torsion-free
group realizes the incidence pattern of `(E,F)`.

**Equivalent forms** (artifact, Proposition 5, using the transfer lemma of
`shannon-window-fakes-transfer-to-canonical-hosts`).

- The claim holds if and only if `LP_{H_P}(E_P, F_P) >= 1` for the canonical host `H_P` of every pattern `P` that
  some torsion-free group realizes.
- A realization is a homomorphism `H_P -> K` that satisfies finitely many inequations, and `H_P` is finitely
  presented. So by `finite-torsion-free-pattern-realizable-finitely-presented` it is enough to consider finitely
  presented torsion-free realizations.

**Consequence.** It implies `torsion-free-windows-have-minimal-shannon-certificates`: a fake in a torsion-free group
realizes its own pattern. Through that claim it would give Bernoulli Rokhlin maximality, Gottschalk surjunctivity
and Kaplansky direct finiteness for every torsion-free group.

**How it can fail.** It can fail at two independent places.

- **(P2) entropy side.** Some pattern with a torsion-free realization has `LP_{H_P} < 1`. When `H_P` itself is
  torsion-free, this refutes the torsion-free claim too.
- **(P1) pattern side.** A fake's pattern is realized without torsion even though `H_P` has torsion. This refutes
  only the strengthening, and so kills this route to the torsion-free claim.

**Evidence.**

- Every one of the 151 known fakes, from hosts `Z/3` to `Z/7`, `(Z/2)^2`, `Z/2 x Z/4`, `S_3`, `S_4`, `D_inf`,
  `Z/3 x Z/3` and Heisenberg mod 3, forces torsion by a two-letter relator `u^k` in `H_P`.
- The exhaustive scans cover 1274 patterns, with `|E| <= 4`, `|F| <= 3`, ground set `<= 10`, in groups of order
  `<= 6`. Each pattern either forces torsion or has a free canonical host on which the LP solver returns `>= 1`.
  So the claim holds numerically on all of them.

## Attempts

- **Two-letter certificates are complete (swarm-0917-w4-pull-gs-4, 2026-09-17).** This is not a proof attempt. It
  is a record of how far the pattern side goes.
  - On all 151 fakes, forced torsion shows up as a relator `u^k` where `u` is a window point, a reader ratio or an
    offset ratio.
  - The attack would be: prove that every fake carries such a relator, then use Lemma 4 of the artifact.
  - **It dies at the first step.** Nothing in the LP refers to Tietze normal forms. The census certificates came from
    a search, not from a dual LP solution, so no mechanism links `LP < 1` to a proper-power relator.
  - What is needed is the reverse link: a dual-feasible Shannon derivation of `Phi >= 1` built on `H_P` whenever
    `H_P` has no such relator. That is the entropy side (P2), and it is open.
- **Orderable-past chain rule (deferred, same agent).** On a left-orderable host, the standard route to `Phi >= 1`
  is the Kieffer-type chain rule
  `H(x_1 | y_F) >= H(x_1 | x_past) - (H(y_F) - H(y_f0))`.
  - **It dies inside the minimal window.** The chain rule conditions on `x_g` for `g < 1`, and those variables
    lie outside `X = FE ∪ {1}`, so the LP cannot state it.
  - Even outside the window it would not reach every torsion-free group: the Promislow group is torsion-free and
    not left-orderable.
  - Free groups are orderable, but the window LP never sees the past variables. So the 723 free-host values
    `>= 1` in `free_host_lp.txt` must come from derivations that stay inside the window, and their dual solutions
    are the natural next object to study.
