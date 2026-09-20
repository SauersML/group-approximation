---
rg: 2
id: birget-bartholdi-mitrofanov-route-review
kind: claim
title: Referee review of 71dff57f58 (Birget via decidable Bartholdi–Mitrofanov hosts) — item (a) holds, but only with Minsky's exponential input encoding (x ∈ X read at n = 2^x, words of length 2^(2^x)), not "a two-counter machine halting exactly on X"; (b) is implied by (c) plus the unchecked Zaremsky transfer, by Kuznetsov; the route answers Birget's question as he wrote it, negatively ("no cap"), and the node's robustness paragraph has the polarity of "negative answer" reversed
distinct_from:
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that is the lane node under review; this checks its item (a), its reduction to Birget's question, and its sources.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that is the root, the "no cap" form of Birget's question; this records Birget's verbatim wording and which answer the route gives.
  finite-recursion-gives-no-computable-depth-bound: that uses Bartholdi–Mitrofanov Theorem A″ as a counterexample; this reads the same paper's §2 at source for the encoding and the direction of Proposition 2.4.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane node by bh-birget, landed in
71dff57f58).** No priority claimed. Sources read on 2026-09-19:
- Bartholdi–Mitrofanov, arXiv:1710.10109, via the ar5iv rendering: Theorems A, A′ and A″, Definition 2.1,
  §2.1, Propositions 2.3 and 2.4, and the proof of A″.
- Birget, arXiv:math/0310335, §1, via ar5iv, checked against the `Thconp.tex` quotation in
  `research/artifacts/hl-bh-hard-simple-2026-09-13.md`.
No code was run.

## 1. Sources

- **Bartholdi–Mitrofanov, at source.**
  - Definition 2.1: two counters `(m, n)`, states `S`, an initial state `s_*` and a final state `s_†`. The machine
    starts at `(s_*, 0, 0)` and halts on reaching `s_†`.
  - §2.1: the configuration `(s_i, m, n)` is encoded as `s_i x^(2^m) y^(2^n)`.
  - Proposition 2.4, stated for the initial configuration: "M halts if and only if
    `[(s_* x y) t (s_* x y)^(-1), u] ≠ 1`". So the direction is **nontrivial iff halts**.
  - Theorem A″'s proof uses a universal machine that emulates Turing machines "encoded in an integer `n`, when
    started in state `(s_*, 0, n)`". It uses the words `w_n = [(s_* x y^(2^n)) t (s_* x y^(2^n))^(-1), u]`, of
    length `Θ(2^n)`.
  - The node's paraphrase is correct, including "trivial for exactly one of the two outcomes". One precision:
    Proposition 2.4 is proved for `(s_*, 0, 0)`, and its use at `(s_*, 0, n)` is how the proof of A″ applies it.
- **Birget, verbatim** (math/0310335, §1). The question is "Is there some cap on the computational complexity of
  the word problem of finitely presented simple groups?" The consequence he draws from the conjecture he
  attributes to Higman: "for every function `T` which is the time complexity of a deterministic Turing machine,
  there is a finitely presented simple group whose word problem cannot be decided in time `≤ T`." He also records
  the transfer the node's step 4 uses: a finitely generated subgroup "cannot have higher complexity than `S`, up to
  linear changes in the complexity function."

## 2. Item (a): correct in substance; one step must be repaired

- **The reduction is right.** An algorithm for `WP(⟨Φ_M⟩)` in time `C·T(C·l) + C·l + C` decides
  `X_M = {n : M halts from (s_*, 0, n)}` in time `C·T(C′·2^n) + O(2^n)`, since `w_n` is written in `O(2^n)` steps.
  So (a) holds whenever `X_M ∉ DTIME(T′)` for a recursive `T′` dominating every
  `n ↦ C·T(C′·2^n) + C′·2^n + C`. The hardness has to be measured after the exponential rescaling, which the
  node's argument does, though its headline "whenever the halting set is hard" does not say so.
- **The faulty step.** "Minsky's simulation gives a two-counter `M` that halts exactly on `X`."
  - With the input read directly as the counter value `n`, this is not available in general. By Schroeppel (MIT
    AI Memo 257, 1972; recalled), a two-counter machine cannot compute `n ↦ 2^n`. Minsky's universality of two
    counters works through the Gödel encoding `2^a 3^b 5^c ⋯` of a multi-counter machine's registers.
  - Bartholdi–Mitrofanov's own universal machine likewise reads an *encoded* integer.
- **Repair.** Let `D` be a multi-counter machine deciding `X`, total on all inputs, which enters an explicit loop
  on rejection. Minsky's two-counter simulation `M` of `D` satisfies "`M` halts from `(s_*, 0, 2^x)` iff `x ∈ X`".
  The words `w_(2^x)` have length `Θ(2^(2^x))`, so an algorithm for WP in time `T(l)` decides `X` in time
  `T(C·2^(2^x)) + O(2^(2^x))`.
- **The time hierarchy still applies.** Take `T″(x)` recursive and dominating `C·T(C·2^(2^x)) + C·2^(2^x) + C` for
  every `C`. The hierarchy theorem gives a decidable `X ∉ DTIME(T″)`, so (a) holds.
- Only this doubly exponential rescaling changes; the conclusion of (a) stands.

## 3. The reduction to Birget's question

- **What (a)+(b)+(c) give, with step 3.**
  - (c) and `lift-ideal-criterion-sufficiency-holds-for-infinite-state` make `V_d(G)` finitely presented.
  - `[V_d(G), V_d(G)]` is simple (Nekrashevych).
  - Zaremsky's regrouping and wreath steps are needed to place `G` in a finitely presented simple group. This is
    step 3, correctly flagged as unchecked: it is stated for finitely presented `G`, and it must be rerun for "relator
    kernel a finitely generated lift ideal". The abelianization of `V_d(G)` can be infinite when `G^ab` is, so the
    commutator subgroup need not have finite index without it.
  - Step 4 is Birget's own linear transfer, so hardness of `G` passes to the host with constants.
  - Result: for every recursive `T`, a finitely presented simple group whose word problem cannot be decided in time
    `≤ T`. That is Birget's stated consequence verbatim, since "time complexity of a deterministic Turing machine"
    functions are recursive.
- **(b) is redundant.** Every finitely generated subgroup of a finitely presented simple group has solvable word
  problem (Kuznetsov). So (c) together with step 3 already implies (b).
  - (b) is still worth keeping as the first obstruction test.
  - For Theorem A″'s universal machine, whose word problem is undecidable, (c) must fail, or step 3 must fail
    for it. That is a free calibration case for the node's first test 1.
- **Polarity (repair).** Birget's question is "Is there some cap?"
  - This route answers it **negatively**: there is no cap.
  - The node's Robustness item 1 calls a cap "a negative answer to Birget's question", which reverses Birget's
    wording. Replace it with "a cap (a positive answer to Birget's question) would give one recursive bound …".
- **Not claimed, correctly.** The route does not give the stronger conjecture Birget attributes to Higman, which is
  Boone–Higman.

## 4. Other items

- **Robustness items 2–4** are correct as stated. `V_d(G) ⊇ V_d` is never residually finite, so a cap on finitely
  presented self-similar groups cannot touch it.
- **The classical-families paragraph** quotes KMS's abstract correctly, as "as of 2013".

## Verdict

**PASS with repairs** for what the node claims: an OPEN sufficient condition with item (a) proved.
- (a): repair the two-counter step to Minsky's encoded input `n = 2^x`. The conclusion survives via a doubly
  exponential rescaling in the hierarchy argument.
- (b): note that it is implied by (c) plus step 3.
- Fix the polarity of "negative answer" in Robustness item 1.
- Step 3, the Zaremsky transfer for lift-ideal kernels, stays the one unchecked link, as the node says.
