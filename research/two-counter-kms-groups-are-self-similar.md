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
  kms-tops-are-fp-transitive-self-similar-for-odd-p: that makes the top Q of every KMS group with p odd finitely presented and self-similar; this asks for the whole group G(M) = T x| Q, so the configuration layer T is what remains. (The route hard-self-similar-groups-via-self-similar-kms-modules, formerly listed here, needs the dead lamp-digit premise; this is the same payoff through any faithful recursion.)
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
  `two-counter-kms-top-has-no-affine-self-similar-action`. It holds only in the sense of that node, where every
  counter acts by a causal linear map. Kochloukova–Sidki-type actions, in which some counters move the root, escape
  it: see Attempts.
- **Depth-preserving extensions only.** In any ascending-HNN step inside `Aut(T_d)`, every level profile is
  preserved (`self-similar-higman-routes-meet-krull-dimension-two`, Lemma 1).
- **Two counters, so Krull dimension at least 2, in characteristic `p`.**
  - For the top factor this is computed: `R_K = F_p[s_i^{±1}, (1 − s_i)^{-1} : i ≤ K]` is a localization of
    `F_p[s_1, …, s_K]`, so it has Krull dimension `K` (`two-counter-kms-top-has-no-affine-self-similar-action`).
    For the configuration module it is a heuristic.
  - One counter is easy: one-counter automata have NL-complete reachability for unary updates
    (Lafourcade–Lugiez–Treinen 2004, as stated in the counter-automata literature), while two counters are Turing
    complete (Minsky 1967).
  - The characteristic-0 analogue has non-self-similar finitely presented metabelian examples (Kochloukova–Luiz,
    arXiv:2509.05798, Main Theorem). Their hypotheses, verbatim, are: `G = A ⋊ Q` with `Q ≅ ℤ^s`, `s ≥ 2`, and
    (1) "A is a cyclic ℤQ-module, say A≃ℤQ/I, A is a ℤ-torsion-free integral domain and Krulldim(A)=2";
    (2) "for every prime number p the ring A/pA is an infinite integral domain"; (3) "the image of a non-trivial
    element of Q in the field of fractions of A is not algebraic over ℚ. In particular C_Q(A)=1_Q"; (4) "G is
    finitely presented".
  - Krull dimension 1 is self-similar (Kochloukova–Sidki, arXiv:1710.04745, Theorem C), but one counter is easy.
  - **Characteristic `p` in Krull dimension `d ≥ 2` is also self-similar.** Kochloukova–Sidki's Theorem D in the
    same paper covers it, and for `p` odd it contains the KMS tops `B_K`, embedded with index 2 in finitely
    presented self-similar groups: `kms-tops-embed-in-fp-self-similar-metabelian-groups`.
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
   on the `p^2`-adic tree (Dantas–Sidki, arXiv:1505.05165, J. Algebra 2018; for `d ≥ 2` there is none on the
   `p`-adic tree). It is not finitely presented, so it is only a starting point. Test whether its virtual endomorphism survives adding one
   BR-conjoint letter `x ↦ x(a − 1)`. That is the smallest step toward a two-counter configuration module.

## Attempts

**Attempt 1 (2026-09-19, lane paradigm/decomposition, family linear-characteristic): both first tests are
resolved, and the crux is localized to `T`.** See `kms-tops-are-fp-transitive-self-similar-for-odd-p`
(ESTABLISHED).

- **The identification.** Relation G4 says that `ã_i^{-1}` acts on the lamp `A_0` as `1 + (ã_i')^{-1}`. With
  `x_i = (ã_i')^{-1}` and `y_i = ã_i^{-1}`, this identifies:
  - `B_0 ≅ KS_K(1 + x)`, the Kochloukova–Sidki Theorem D group with `g = 1 + x`;
  - `B_i ≅ KS_1(1 + x)`.

  This is the Möbius substitution `x = s^{-1} − 1` on `R_K`.
- **The top.** For `p` odd, the whole top `Q` is finitely presented and transitive self-similar, by KS Lemma 7.2,
  Lemma 7.4 and products.
- **Test 1 dies.** `B_0` with `K = 2` satisfies the characteristic-`p` analogues of Kochloukova–Luiz conditions 1,
  3 and 4, and it is self-similar. It is the reduction mod `p` of their own non-self-similar Example 2.
- **Test 2 is answered positively.** The Dantas–Sidki map survives the BR-conjoint letter after localization at
  `1 + x`.
- **Where the crux now sits.** `Q` is a retract of `G(M)`, but a simple virtual endomorphism of `G(M)` need not
  restrict to a simple one of `Q`. So this is not a step of a route. What it shows is that no obstruction to
  KD2_p can come from the top alone. Any obstruction lives in `T` and in its gluing by G5–G8.
- **Unfinished observation on the gluing (not established).**
  - The Kochloukova–Sidki map cycles the counters of `B_0`: `ã_1^p ↦ ã_2`, and so on.
  - On `B_i` it sends `a_i^p ↦ a_i`.
  - G6 makes `c_i = a_i ã_i^{-1}` centralize every `x_{q_j}`.
  - A `T`-preserving extension `φ` with this top part would send `C_T(c_1^p) ∩ H` into `C_T(a_1 ã_2^{-1})`. On
    unmarked configurations, `a_1 ã_2^{-1}` acts as `a_1 a_2^{-1}`, which has no nonzero fixed points on the free
    part of the counter module.
  - So such an extension would have to push the unmarked configurations into marked ones, or into its kernel.
  - A counter-cycling top therefore seems incompatible with G6 unless the extension is very degenerate. The
    remaining option is a top map on `B_0` matched coordinatewise to the `B_i`, which is not simple on `B_0` alone.
  - This was not carried to a proof.
- **`p = 2` is not covered.** The identification needs `g(1) ≠ 0`.

- **Both first tests, lane bh-kd2p, 2026-09-19** (`kms-tops-embed-in-fp-self-similar-metabelian-groups`; lane proof
  resting on Kochloukova–Sidki Theorem D, not independently reviewed). The crux stays **OPEN** for the whole group
  `G(M)`, but its metabelian top is not an obstruction.
  - **Test 1, kill: negative.** The Kochloukova–Luiz ideal-preservation argument uses characteristic 0 in
    hypotheses (1)–(2) and in Step 5 of its proof. It does not transfer to characteristic `p`: Kochloukova–Sidki
    Theorem D (arXiv:1710.04745) gives finitely presented, characteristic-`p`, Krull-dimension-`d`, transitive
    self-similar metabelian groups `⊗ F_p[x_i^{±1}, 1/g(x_i)] ⋊ ℤ^{2d}`. K–L flag this themselves.
  - **Test 2, start: superseded, and positive.** No need to grow `C_p ≀ Z^2` one letter at a time.
    - For `p` odd, `s_i ↦ −x_i` identifies the KMS top `B_K` with an index-2 subgroup of Theorem D's group for
      `g = 1 + x`, extended by the central scalar `−1`. That extension is finitely presented and transitive
      self-similar.
    - The KMS choice `g = x − 1` is exactly the case Theorem D excludes. The substitution moves the relevant point
      from `1` to `−1`.
    - The affine kill (bh-free-25) assumes all of `U_K` acts linearly. Theorem D's domain meets the counters in a
      subgroup of index `p^2`, a Frobenius-twisted cyclic shift of the counters.
  - **Remaining crux, sharpened.** Lift a Kochloukova–Sidki-type structure from `B_0` to the full top `Q` and
    through the exponent-`p` configuration module `T` of `G(M) = T ⋊ Q`. The coinvariants kill applies only to
    lamp-digit shapes, not to actions that mix lamps with positions. For `p = 2` the KMS top is not covered by
    this route.
