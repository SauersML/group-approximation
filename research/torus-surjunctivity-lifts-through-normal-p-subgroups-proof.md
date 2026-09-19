---
rg: 2
id: torus-surjunctivity-lifts-through-normal-p-subgroups-proof
kind: route
title: Restrict to the fixed torus of the normal subgroup, get a unit image degree there, and lift it mod p through the nilpotent kernel ideal of a finite normal p-subgroup
target: torus-surjunctivity-lifts-through-normal-p-subgroups
requires:
  - torus-automata-with-regular-degree-are-surjective
  - torus-automata-over-rf-or-domain-groups-are-surjunctive
  - torus-degree-regular-on-prime-power-residual-support
artifacts:
  - research/artifacts/torus-normal-p-lifting-2026-09-17.md
  - experiments/torus-normal-p-lifting-2026-09-17/check_normal_p_lifting.py
---

Artifact Sections 1–2.

1. **Restriction (Lemma 1).** `Fix(N)` is closed, `G`-invariant and `tau`-invariant, and
   `i_N : (T^d)^(G/N) -> Fix(N)` is an equivariant homeomorphism. The computation
   `i_N^* = p_N` on `H^1` from the proof of the periodic-point lemma of
   `torus-automata-over-rf-or-domain-groups-are-surjunctive` never uses finite index. So
   `tau_N` is an injective torus automaton over `G/N` of degree `p_N(D)`.
2. **Bijective means unit degree (Lemma 2).** The inverse of a bijective torus automaton is
   a torus automaton, and `D(a o b) = D(a) D(b)`.
3. **Lifting (Lemma 3).** Lift an inverse of `p_N(D) mod p` to `E`. Then `D-bar E = 1 - M`,
   `E D-bar = 1 - M'`, with entries in `F_p[G] omega(P)` for one finite `P <| G`, `P <= N`.
   Normality makes this a two-sided ideal with `k`-th power `omega(P)^k F_p[G]`, zero by
   the nilpotence lemma (Lemma 2) of the artifact of
   `torus-degree-regular-on-prime-power-residual-support`. So `D-bar` is invertible, and a
   `p`-primitive integral kernel vector of `D` would reduce to a nonzero kernel vector of
   `D-bar`.
4. **Closure (Theorem 4, Corollaries 5–6).** If `tau_N` is onto, Lemma 2 makes `p_N(D)`
   a unit, Lemma 3 makes `D` regular, and `torus-automata-with-regular-degree-are-surjective`
   makes `tau` onto. Chains follow by descending induction. A finite solvable normal `L`
   has a chain of `G`-normal subgroups with `p`-group factors (derived series refined by
   Sylow parts, all characteristic).
5. **Check.** The experiment verifies Lemma 3 exactly on `Z/6`, `S_3`, `A_4`, `Z/2 x Z/6`
   (exhaustively on a coefficient box for `Z/6`, randomly at `d = 1, 2` elsewhere).
