---
rg: 2
id: fp-simple-group-with-pspace-complete-word-problem
kind: claim
title: Some finitely presented simple group has a PSPACE-complete word problem
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups beyond every recursive time bound; this asks for one fixed rung, PSPACE-completeness, which the finite-state (automaton) host program can reach and cannot exceed.
  leavitt-square-units-have-conp-parity-p-complete-word-problem: that pins (L ⊗ L)^x at coNP^⊕P, conditionally on its host node; this is the next rung, PSPACE, which contains coNP^⊕P and equals it only if PSPACE = P^#P.
  automaton-tail-full-groups-have-conp-relative-word-problem: that proves the PSPACE ceiling for finite-state hosts; this is the matching existence question at the ceiling.
---

**OPEN.** There is a finitely presented simple group whose word problem, over some (hence every)
finite generating set, is PSPACE-complete under polynomial-time many-one reductions.

## Why it matters: the complexity ladder of host programs

Each host family used for Boone–Higman has a word-problem ceiling. By the length-linear substitution
of `complexity-bounded-host-classes-are-not-universal-proof`, the ceiling also bounds every group the
family can host.

| rung | host family | ceiling, and why | reached by |
|---|---|---|---|
| coNP | `nV`, and `FV(H_1, …, H_n)` with coefficient groups in P | `automaton-tail-full-groups-have-conp-relative-word-problem` (one guessed cylinder of polynomial depth, monomial evaluation) | `2V` (Birget, coNP-complete) |
| coNP^⊕P | units of `L^{⊗d}` over `F_2` | polynomial-depth witnesses with superposed evaluation mod 2 (`leavitt-square-units-have-conp-parity-p-complete-word-problem`, §6) | `(L ⊗ L)^x`, fp simplicity conditional on its host node |
| PSPACE | `V_d(G)`, `FV(H_1, …, H_n)` over automaton groups | `automaton-tail-full-groups-have-conp-relative-word-problem`, item 2 (`coNP^PSPACE = PSPACE`) | **open: this claim** |
| beyond | needs infinite-state coefficient groups | the finite-state ceiling above | `fp-simple-groups-with-arbitrarily-complex-word-problem` |

- **The mechanism.** The rung is set by two things: the depth of a witness point where a nontrivial
  element acts nontrivially, and the mode of evaluation along it.
  - Polynomial depth with deterministic evaluation gives `coNP`.
  - Polynomial depth with evaluation superposed mod 2 gives `coNP^⊕P`.
  - Exponential depth under finite-state recursion gives `PSPACE`. This is the depth `|Q|^n` of
    Wächter–Weiß.
- **The PSPACE input exists.** A PSPACE-complete group already lives in the automaton world:
  `finite-commutator-wachter-weiss-groups-are-not-fp` exhibits a PSPACE-complete `H_R` inside the
  automaton group `G_R`. So the finite-state host program would realize this claim as soon as it
  hosts one Wächter–Weiß group. It can never realize the rung above.

## Routes

- `pspace-fp-simple-via-lift-presented-automaton-overgroups`: from
  `automaton-groups-embed-in-lift-presented-automaton-groups`, applied to a Wächter–Weiß group. That
  premise is needed only for the single input `G_R`: some lift-presented automaton group containing
  `G_R` suffices.
- The simplest instance of that premise, `G_R` with its own action, requires `V_2(C)` to be finitely
  presented, for the binary check-mark automaton group `C`
  (`lift-presentation-passes-to-invariant-subalphabets`). Whether it is has not been decided.
  - *Progress (bh-free-02).* The one-configuration layer of the unencoded `C` is lift-presented by two
    commutators (`single-configuration-check-mark-group-is-lift-presented`), despite exponential
    activity and non-contraction.
  - *The crux.* The configuration layer contains a lamplighter `⟨K, N⟩ ≅ Z ≀ Z`, persistent along
    `0^ω`. Its relators are fixed by the section at `0` and can enter a lift ideal only by normal
    closure (`research/artifacts/gq-bh-bh-free-02-check-mark-layers.md`). Unresolved.

## Lesson for general BH

- **Stratification.** Host programs for Boone–Higman are stratified by complexity class, and each
  program is non-universal above its rung. The finite-state program (Röver–Nekrashevych groups of
  automaton groups) is exactly the PSPACE rung.
- **What a universal proof needs.** A proof of the full conjecture has to use hosts whose elements
  evaluate witness points in a non-finite-state way, consuming the input's algorithm, as
  `compilers-cannot-drop-the-decidability-hypothesis` says. The finite-state program at best settles
  the automaton-group case, and with it this claim.

## Attempts

1. **Clopen towers of twisted Brin--Thompson groups (2026-09-19, lane swarm-0917-w18-w18-bh-break).**
   *Climbs PH, stops short of PSPACE.*
   - **Result.** `twisted-brin-thompson-towers-have-pi-k-complete-word-problems` (ESTABLISHED, lane
     proof, unreviewed). The `k`-th tower `G_k` (`G_1 = 2V`, `G_(k+1) = SV_(G_k)` over clopen sets)
     is finitely presented and simple, with a `Π_k^p`-complete word problem, unconditionally.
   - **Effect on the rung table above.** Between coNP and PSPACE there is now an unconditional
     `Π_k^p` rung for every `k`. The coNP^⊕P rung is not the only candidate step above `nV`.
   - **Where it dies for this claim.** The hardness reduction for `G_k` has length about `4^k` times
     polynomial, because each level uses the previous level's word a bounded number of times. So no
     single `G_k` is PSPACE-hard unless PH collapses to level `k`.
   - **What PSPACE would need.** An infinite tower is not finitely presented. A PSPACE-complete
     group along this line needs one finitely presented actor that contains its own clopen tower
     uniformly, with polynomial-length self-similarity of the amplification step. No candidate is known.
1. **Own action of `G_R` as the lift-presented overgroup (2026-09-17, swarm-0917 belief breaker).** This
   is step 2 of `pspace-fp-simple-via-lift-presented-automaton-overgroups`, using its "first
   candidate". Dead for `L ≢ 2 (mod 3)`, conditional on Theorem A of
   `rover-nekrashevych-fp-iff-finite-lift-presentation`.
   - `wachter-weiss-check-mark-automaton-is-not-lift-presented` shows that the germ group of the
     check-mark group at `0^ω` is `(Z ≀ Z) × Z`. This holds unencoded, and for the binary encoding with
     `|Γ| = 2^L`, `L ≢ 2 (mod 3)`. So `V_2(C)` is not finitely presented, and `V_{|Σ|}(G_R)` is not
     either.
   - The obstruction comes from the skip state `K`: the one-configuration layer is lift-presented.
   - For `L ≡ 2 (mod 3)`, persistent misaligned γ-phases enlarge the germ group. Whether it is finitely
     presented is open.
   - Otherwise step 2 needs a genuinely new overgroup, one whose germs at the check-mark rays are
     finitely presented, for example one that enlarges the lamplighter germ `⟨A, K⟩` to a finitely
     presented germ group.
