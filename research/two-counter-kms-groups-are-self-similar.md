---
rg: 2
id: two-counter-kms-groups-are-self-similar
kind: claim
title: (KD2_p) For every recursive time bound T there are a prime p and a sym-universally halting Minsky machine M with at least two glasses, whose accepted set is not decidable in time T, such that the Kharlampovich–Myasnikov–Sapir group G(M) embeds in a finitely generated self-similar group that is finitely presented, e.g. G(M) is itself self-similar; necessarily through a non-affine, depth-preserving recursion in characteristic p and Krull dimension at least 2
distinct_from:
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that is the general target; this is its concrete KMS instance, which implies it, and it names the only mechanism (depth-preserving, Krull dimension at least 2, characteristic p) that the recorded attempts leave open.
  self-similar-higman-routes-meet-krull-dimension-two: that attempt record localizes the ascending-HNN route; this is the named crux it arrives at.
  two-counter-kms-top-has-no-affine-self-similar-action: that kills affine realizations of the two-counter KMS top; this asks for a non-affine realization of the whole group, or of an fp self-similar overgroup.
  kms-configuration-modules-carry-self-similar-structures: that is the lamp-digit premise, made false by kms-configuration-modules-have-trivial-coinvariants; this allows any recursion on digits and any finitely presented self-similar overgroup.
  hard-self-similar-groups-via-self-similar-kms-modules: that route needs the dead lamp-digit premise; this is the same payoff through any faithful recursion.
---

**OPEN (named crux, lane bh-gate1-abstract, 2026-09-19).**

## Exact statement

For every recursive `T: N → N` there exist:
- a prime `p`;
- a sym-universally halting Minsky machine `M` with `K ≥ 2` glasses, whose accepted set is not decidable in time
  `T`;
- `d ≥ 2`;

such that the KMS group `G(M)` of arXiv:1204.6506v5 §4.1, built with the prime `p`, embeds in a **finitely
presented**, finitely generated self-similar group `S ≤ Aut(T_d)`. The simplest case is `S = G(M)` with a faithful
self-similar action.

KMS Thm 4.17 and Thm 4.18 make `G(M)` finitely presented and residually finite, with word problem at least as
hard as the halting problem for `M`.

## Forced features (from main)

- **Infinitely many states.** Finite-state groups have word problem in PSPACE, by item 4 of
  `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.
- **Non-affine on digits.** This follows from `affine-self-similar-groups-are-function-field-linear` and
  `two-counter-kms-top-has-no-affine-self-similar-action`.
- **Depth-preserving extensions only.** In any ascending-HNN step inside `Aut(T_d)`, every level profile is
  preserved (`self-similar-higman-routes-meet-krull-dimension-two`, Lemma 1).
- **Two counters, so Krull dimension at least 2, in characteristic `p`.**
  - The characteristic-0 analogue has non-self-similar finitely presented metabelian examples (Kochloukova–Luiz,
    arXiv:2509.05798).
  - Krull dimension 1 is self-similar (Kochloukova–Sidki 2020, as quoted there), but one counter is easy.
- **Residual `W_d` and depth are no obstruction.**
  - `G(M)` acts faithfully on `T_7` for `p = 2` (`finite-class-kms-groups-act-on-regular-rooted-trees`).
  - Any such action has super-recursive nontriviality depth
    (`farley-hughes-certificates-have-prefix-chart-coordinates`, the KMS section).

## What it would give

- **The hard-WP target.** `fp-self-similar-groups-with-arbitrarily-hard-word-problem` follows at once, with `S`.
- **Birget's question.** `fp-simple-groups-with-arbitrarily-complex-word-problem` follows through
  `arbitrarily-complex-fp-simple-via-hard-self-similar-groups` (Zaremsky's embedding).
- **Gate 1 via Farley–Hughes, word-problem channel.**
  - `V_d(S)` is finitely presented by Scott's theorem, as imported in `rover-nekrashevych-finite-presentation-criteria`.
    It is plausibly also FH-certifiable with structure group `S`: maximal S-structure, the standard `V_d`
    expansion scheme, and Prop. 8.10 with `n = 2`. That is a lane sketch, not checked.
  - Its word problem is at least that of `G(M)`.
  - So KD2_p supplies exactly the one hardness channel that
    `farley-hughes-certificates-have-prefix-chart-coordinates` leaves open for nested certificates. The seed
    channel stays dead.
  - Whether the resulting host carries a type (A) action as HARD-(A) requires is **not checked** here.

## Suggested first tests

1. **Transfer the Kochloukova–Luiz argument to characteristic `p`.** Their proof shows that virtual endomorphisms
   must preserve nontrivial ideals. Does that step survive for `F_p`-modules of Krull dimension 2? If it does,
   KD2_p dies for metabelian tops, and the two-counter KMS top would need a non-metabelian overgroup.
2. **Characteristic-`p` Krull-dimension-2 self-similarity is possible in principle.** `C_p ≀ Z^2` is self-similar
   (Dantas–Santos–Sidki; recalled, not re-read). Test whether its virtual endomorphism survives adding one
   BR-conjoint letter `x ↦ x(a − 1)`. That is the smallest step toward a two-counter configuration module.
