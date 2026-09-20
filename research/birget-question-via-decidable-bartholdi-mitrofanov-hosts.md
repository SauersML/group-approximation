---
rg: 2
id: birget-question-via-decidable-bartholdi-mitrofanov-hosts
kind: claim
title: Decidable Bartholdi–Mitrofanov groups beyond every time bound whose relator kernel is a finitely generated lift ideal; they would answer Birget's question through Röver–Nekrashevych hosts, a route that no cap on finitely presented self-similar groups can block
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is Birget's question itself; this is a sufficient condition for it, through V_d(G) for a functionally recursive G, and it never needs a finitely presented self-similar group.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that asks for finitely presented self-similar (hence residually finite) hard groups; this asks for non-finitely-presented functionally recursive hard groups with a finitely presented V_d(G), which is never residually finite.
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that is the self-similar Higman step; its test-input section says the graph does not establish that decidable hard functionally recursive groups exist, and items (a) and (b) here are exactly that existence question for one explicit family.
  two-counter-kms-groups-are-self-similar: that starts from KMS groups, which are finitely presented and residually finite but not known to be self-similar; this starts from Bartholdi–Mitrofanov groups, which are functionally recursive by construction but not finitely presented.
  finite-recursion-gives-no-computable-depth-bound: that uses the undecidable Bartholdi–Mitrofanov group to show depth is unbounded; this asks for decidable members of the same family.
  nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups: that keeps the whole free group and gets a finitely presented non-faithful host with a non-recursive kernel; this asks for the faithful quotient V_d(G) to be finitely presented.
---

**OPEN.** For every recursive `T: N -> N` there is a functionally recursive group
`G = ⟨Φ⟩ ≤ Aut(T_d)` (a finite map `Φ: A × S -> F_S × A`, in the notation of
`finite-recursion-gives-no-computable-depth-bound`) such that

- **(a)** `WP(G)` has no algorithm running in time `C·T(C·l) + C·l + C` for any `C`;
- **(b)** `WP(G)` is solvable;
- **(c)** the relator kernel `N = ker(F_S -> G)` is a finitely generated lift ideal.

Lane bh-birget, 2026-09-19. Nothing below is independently reviewed; no priority is claimed.

## Why it would answer Birget's question (sketch; one transfer unchecked)

1. By (c) and `lift-ideal-criterion-sufficiency-holds-for-infinite-state` (item 1, referee PASS),
   `V_d(G)` is finitely presented.
2. `[V_d(G), V_d(G)]` is simple for every self-similar `G`
   (`rover-nekrashevych-finite-presentation-criteria`, item S).
3. Zaremsky's regrouping and wreath steps (same node, item R; arXiv:2405.09722, proof of Theorem 1.1) then
   place `G` inside a finitely presented simple commutator subgroup of finite index. **Not checked:** those
   steps are stated for finitely presented `G`; here they must be rerun with "relator kernel a finitely
   generated lift ideal" in place of "finitely presented". Regrouping keeps the sections, so it should keep a
   finite lift-generating set, but nobody has verified this.
4. The upward transfer of `arbitrarily-complex-fp-simple-via-hard-self-similar-groups` (step 3) then carries
   (a) to the simple host.

## What is known toward (a), (b), (c)

**The family.** Bartholdi–Mitrofanov, arXiv:1710.10109 (Groups Geom. Dyn. 2020), §2, attach to every
two-counter Minsky machine `M` a functionally recursive group `⟨Φ_M⟩`. Read via the ar5iv rendering of the
arXiv source on 2026-09-19, as a paraphrase, not verbatim; a referee should check it at source.
- Configurations `(s_i, m, n)` are encoded by the words `s_i x^(2^m) y^(2^n)`. Sections simulate the moves
  of `M`, and a halting marker is written when `M` reaches its halting state (their Prop. 2.3).
- A commutator `w_n` built from the encoding of `(s_*, 0, n)` has length `O(2^n)`. It is trivial for exactly
  one of the two outcomes "M halts from `(s_*, 0, n)`" or "it does not" (their Prop. 2.4).
- Theorem A″ takes a universal `M`.

**(a) holds for every member where the halting set is hard.** This uses only that `w_n`'s triviality records
halting, not which way. Let `X = {n : M halts from (s_*, 0, n)}`. An algorithm for `WP(⟨Φ_M⟩)` in time `T(l)`
decides `X` in time `T(C·2^n) + O(2^n)`. By the time hierarchy theorem, some decidable `X` beats every
recursive bound of this form. Minsky's simulation gives a two-counter `M` that halts exactly on `X`: it runs
a decider for `X`, halts on accept and enters an explicit loop on reject. If `WP` is undecidable, (a) holds
trivially.

**(b) is open.**
- **What is automatic.** Nontriviality is r.e., because the action is computable and faithful. By
  `finite-recursion-gives-no-computable-depth-bound`, (b) is equivalent to a computable bound on the depth
  function.
- **Where it can fail.** Bartholdi–Mitrofanov analyze only configuration words. Other words, such as
  `s_i x^k` with `k` not a power of `2`, or products of several encodings, run `M`-like dynamics from
  configurations that `M` never reaches, and some of those runs may never halt.
- **The natural hypothesis.** "Halting of `M` from every configuration is decidable, and every word's
  section dynamics is a finite superposition of configuration runs." This mirrors the sym-universally
  halting machines that Kharlampovich–Myasnikov–Sapir needed for residual finiteness (arXiv:1204.6506), and
  their machine lemma is the likely input. It is not checked.

**(c) is open.** A heuristic, not proved:
- In `⟨Φ_M⟩` the section map *is* one machine step. So lifting a relator of an encoded configuration
  produces relators of the next configurations of the same run.
- That suggests `N_M` is lift-generated by finitely many transition-local relators, plus relators for the
  halting configurations `(s_†, m, n)`.
- This contrasts with persistent actions (`persistent-actions-make-lift-ideals-normal-closures`), where
  lifting gives nothing. It also meets the design constraint of bh-invent-03 (182261ea21): relators must
  contract while elements do not, since here the elements' encodings grow along runs.

## Robustness: this route survives any cap on finitely presented self-similar groups

Elementary, lane proof.
1. **A cap for finitely presented simple groups refutes Boone–Higman.** A negative answer to Birget's
   question would give one recursive bound for all finitely presented simple groups. By
   `complex-fp-simple-groups-from-boone-higman`, that refutes Boone–Higman, so a negative answer is exactly
   as strong as a counterexample to Boone–Higman.
2. **A cap for finitely presented self-similar groups is not known to conflict with Boone–Higman.**
   - Those groups are residually finite (`self-similar-hosts-contain-only-residually-finite-groups`).
   - Boone–Higman's hosts are infinite simple, hence never residually finite.
   - No implication from Boone–Higman to hard finitely presented self-similar groups is known.
3. **What such a cap would kill.**
   - It would kill `fp-self-similar-groups-with-arbitrarily-hard-word-problem`, the route
     `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`, and the payoff of
     `two-counter-kms-groups-are-self-similar`.
   - With (a) and (b), it would refute `decidable-fg-self-similar-groups-embed-in-fp-self-similar`: a
     finitely presented self-similar host of `G` would beat every bound.
4. **It would not touch this route.** `V_d(G)` contains `V_d`, so it is never residually finite, and it lies
   outside the capped class.

## Classical hard groups are not inputs to either self-similar channel

Collins–Miller's aspherical constructions, Boone–Britton groups, and S-machine groups (Sapir–Birget–Rips;
Birget–Olshanskii–Rips–Sapir, Annals 2002) give finitely presented groups with any prescribed degree or
complexity. But every subgroup of `Aut(T_d)` is residually finite, and KMS state that their groups are "the
first examples of an algorithmically complex finitely presented residually finite groups" (arXiv:1204.6506,
abstract). So as of 2013 none of the classical families was known to be residually finite. They can enter
neither the self-similar channel nor this one as they stand. They matter only for the non-self-similar
channels the root already tracks: type (A) actors and Leavitt unit groups.

## First tests

1. **Calibrate (c) on the smallest machine,** one halting state and no instructions: is `N_M` a finitely
   generated lift ideal?
2. **The same for a one-counter loop,** checking whether the halting-configuration relators
   `(s_†, m, n)`, for all `m, n`, are lift-generated by finitely many.
3. **Read Bartholdi–Mitrofanov §2 at source,** and settle what non-configuration words do. That decides
   whether (b) needs more than decidable halting from every configuration.

## Credit

- **The family and the simulation:** Bartholdi and Mitrofanov.
- **The machine hypotheses:** Kharlampovich–Myasnikov–Sapir.
- **The lift-ideal criterion:** bh-invent-03 (refereed by bh-ref-q12).
- **Naming the V_d route as untested:** bh-gate1-abstract (ed3dbbb573).
- **Birget's question:** arXiv:math/0310335 §1, quoted in `research/artifacts/hl-bh-hard-simple-2026-09-13.md`.
- **The finite-presentation inputs:** Scott, Nekrashevych and Zaremsky.
