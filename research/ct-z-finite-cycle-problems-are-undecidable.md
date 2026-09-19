---
rg: 2
id: ct-z-finite-cycle-problems-are-undecidable
kind: claim
title: In Kohl's class transposition group CT(Z) it is undecidable whether a given element has only finite cycles, and whether it has no finite cycles; this answers Kourovka Problem 21.74(b) and (c) negatively
artifacts:
  - research/artifacts/gq-bh-bh-free-58-kari-ollinger-source.md
---

**ESTABLISHED** (lane proof; referee PASS 2026-09-18 and second referee PASS bh-ref-q11 2026-09-19, both conditional on the published theorems of Kari–Ollinger; see Referee).

- **Inputs.**
  - Kari–Ollinger, MFCS 2008, Theorems 3 and 6, read at source (see the artifact). They
    are published, but the paper gives proof sketches only.
  - The elementary node `ct-z-north-south-element-has-no-finite-cycles`.
- **Membership in CT(Z)** comes from explicit words in class transpositions. It does
  not use `ct-p-z-is-a-one-vertex-k-graph-full-group` or 17.59.
- **Priority.** None is claimed. An arXiv search (class transposition,
  residue-class-wise) found no paper on 21.73 or 21.74. The 21st issue (2026) lists
  both as unsolved.
- **Not settled here.** Part (a) of 21.74, and 21.73.

## Statement

Kourovka 21.74 (S. Kohl) asks whether it is decidable, for a given `g ∈ CT(Z)`,
whether `g`
- (a) permutes a nontrivial partition of `Z` into residue classes;
- (b) has only finite cycles;
- (c) has no finite cycles.

**Theorem.** An algorithm takes a reversible 2-counter machine `M` and outputs words
`F_M` and `H_M` in class transpositions. All moduli in these words are
`{2,3,5,7,11,13}`-smooth, and:

1. `F_M` has only finite cycles on `Z` iff every configuration of `M` is periodic.
2. `H_M` has no finite cycle on `Z` iff `M` has no periodic configuration.

Combined with Kari–Ollinger:
- Theorem 3 (periodicity of complete 2-RCM is undecidable) makes (b) undecidable.
- Theorem 6 (it is undecidable whether a 2-RCM admits a periodic configuration) makes
  (c) undecidable.

Both hold already in `CT_P(Z)` with `P = {3,5,7,11,13}`. They hold whether `g` is given
as a word or as an rcwa map, because the rcwa table of a word is computable.

## The machine (Kari–Ollinger conventions)

- **Machine.** `M = (S, 2, T)` with `S = {1, …, N}`. An instruction `(s, u, i, φ, t)`
  applies to a configuration `(s, v)` whose zero/positive pattern is `u`, and changes
  counter `i` by `φ ∈ {−1, 0, +1}`. `M` is deterministic, `G` is its partial
  transition map, and the reversed table `T^{-1}` is deterministic too.
- **(R1) `G` is injective.** Suppose `G(x) = G(x') = y` by instructions `ι` and `ι'`.
  - Some reversed instruction of `ι` applies at `y`, and one of `ι'` does too. For
    `φ = −` the reverse of `ι` consists of two instructions, and the zero pattern of
    `y` picks one.
  - Both have source state and test vector equal to those of `y`. Since `T^{-1}` is
    deterministic, they have the same action and target.
  - Each maps `y` back to `x` (resp. `x'`), so `x = x'`.
- **(R2) Two finite unions of cells.**
  - `Halt = {x : G(x) undefined}`.
  - `Init = {y : y ∉ G(S × N^2)}`.
  - Both are finite unions of *cells*: a state together with, for each counter, whether
    it is `0`, `1` or `≥ 2`.
  - Reason: an instruction `(s, u, i, φ, t)` maps its domain onto the set of `(t, w)`
    with `w_j` in the class of `u_j` (zero or positive) for `j ≠ i`. The condition on
    `w_i` is:
    - the class of `u_i`, if `φ = 0`;
    - `w_i = 1` or `w_i ≥ 2`, according to `u_i`, if `φ = +`;
    - none, if `φ = −`.

## The element

For `n ≠ 0` let `e_p(n)` be its `p`-adic valuation. We consider `n` with `e_2(n) = 0`
and `1 ≤ e_7(n) ≤ N`.

- **Codes.** Such an `n` is:
  - a *configuration code* if `e_11 = e_13 = 0`; its configuration is
    `c(n) = (e_7, (e_3, e_5))`;
  - a *backward-ray code* if `e_11 ≥ 1`, `e_13 = 0` and `c(n/11^{e_11}) ∈ Init`;
  - a *forward-ray code* if `e_13 ≥ 1`, `e_11 = 0` and `c(n/13^{e_13}) ∈ Halt`.
- **The map.** Let `X` be the set of codes, and define `f : X → X` by:
  - `f(n) = 7^{t−s} 3^{φ_1} 5^{φ_2} n` on configuration codes with `c(n) ∉ Halt`, where
    the applicable instruction goes to state `t` and changes the counters by
    `(φ_1, φ_2)`;
  - `f(n) = 13n` on configuration codes with `c(n) ∈ Halt`, and on forward-ray codes;
  - `f(n) = n/11` on backward-ray codes.

**Claim 1.** `f` is a bijection of `X`, and its finite cycles are exactly the codes of
periodic configurations.

- Write `n = ±w·∏ p^{e_p}` with `w` prime to 2·3·5·7·11·13. Then `f` preserves the sign
  and `w`.
- Fix the sign and `w`. Then `f` acts as follows:
  - as `G` from `Conf ∖ Halt` onto `Conf ∖ Init`, bijectively by (R1);
  - as `j ↦ j+1` on the exponent of 13, from `Halt ∪` forward rays onto forward rays;
  - as `j ↦ j−1` on the exponent of 11, from backward rays onto backward rays `∪ Init`.
- These three domains partition `X`, and so do the three images.
- Along backward-ray codes the exponent of 11 strictly decreases, and only
  backward-ray codes map to backward-ray codes. Forward rays are never left. Hence a
  finite cycle consists of configuration codes, on which `f = G`. ∎

**Claim 2.** Put `L = 2·3²·5²·7^{N+1}·11·13`.
- `X`, and the domain of each formula above, are unions of classes mod `L`. Membership
  reads only `e_2 ∈ {0, ≥1}`, `e_3, e_5 ∈ {0, 1, ≥2}`, `e_7 ∈ {0, …, N, ≥N+1}` and
  `e_11, e_13 ∈ {0, ≥1}`.
- On each class `c(L) ⊆ X` with `0 ≤ c < L`, `f(n) = λ_c n` with `λ_c > 0`. Each
  denominator of `λ_c` divides `n`, hence `c`, because it divides `L`.
- So `f` maps `c(L)` canonically onto the class `(λ_c c)(λ_c L)`, via
  `c + Lk ↦ λ_c c + λ_c L k`. ∎

**The word `F_M`.** Let `K = {c : c(L) ⊆ X}` and put

    s_1 = ∏_{c∈K} τ_{c(L), 2c(2L)},    s_2 = ∏_{c∈K} τ_{2c(2L), (λ_c c)(λ_c L)},    F_M = s_2 s_1.

- **Disjointness.** The classes `c(L)` are odd, so they are disjoint from the classes
  `2c(2L)`, which have `e_2 = 1`. The classes `2c(2L)` are pairwise disjoint. The
  classes `(λ_c c)(λ_c L) = f(c(L))` are pairwise disjoint and partition `X`.
- **The two involutions.** So `s_1` and `s_2` are products of class transpositions with
  disjoint supports. `s_1` is `n ↔ 2n` and `s_2` is `2n ↔ f(n)`, for `n ∈ X`.
- **The composite.** `F_M = f` on `X`, `F_M(2n) = 2f^{-1}(n)` on `2X`, and `F_M` is the
  identity elsewhere. Its cycles are those of `f`, copies of those of `f^{-1}`, and
  fixed points.
- **Proof of 1.** If every configuration is periodic, then `Halt = Init = ∅`, so `X`
  consists of configuration codes and `f = G` has finite orbits. Otherwise a
  non-periodic configuration has an infinite `f`-orbit, by Claim 1.

**The word `H_M`.** Put `L' = 4L`.
- `Y = Z ∖ (X ∪ 2X)` is a union of classes `j(L')`.
- For each such class, let `ψ_j` be the five-transposition conjugate of `ψ` supported
  on `j(L')`, as in item 3 of `ct-z-north-south-element-has-no-finite-cycles`. It has
  no finite cycles on `j(L')`.
- Put `H_M = (∏_j ψ_j) F_M`.
- **Proof of 2.** On `X ∪ 2X`, `H_M = F_M`, and `Y` has no finite cycles. So `H_M` has
  no finite cycle iff `f` has none, i.e. (Claim 1) iff `M` has no periodic
  configuration.

**Computability.** Every modulus used is `{2,3,5,7,11,13}`-smooth. `Halt`, `Init`, `K`,
the `λ_c` and `Y` are all computed from `T` by finite checks mod `L'`. ∎

## Remarks

- **More counters.** Any number of counters works, using one prime per counter.
- **Finite order.** `F_M` has finite order iff `M` is uniformly periodic, which is
  decidable (Kari–Ollinger Thm. 4). So this construction says nothing about the
  torsion problem in CT(Z).
- **21.74(a).** Its yes-instances are recursively enumerable:
  - enumerate the partitions `𝒫`;
  - compute `g(C)` for each `C ∈ 𝒫` and test that it is a class of `𝒫`.

  `ψ` is an explicit no-instance. Every product of multiplicative class maps with odd
  multipliers preserves parity, and so is a yes-instance. Decidability remains open
  here.
- **21.73** (conjugacy) remains open here.
## Lesson for general BH

- **Two involutions suffice.** Every bijection `f` of a periodic set `X`, piecewise a
  canonical class map, lies in a fixed fp simple group `CT_P(Z)` once `f` is doubled to
  `f ⊕ f^{-1}` on a disjoint copy `2X`. It is the product `s_2 s_1` of two involutions,
  each a product of disjoint class transpositions. This is a Bennett-style
  reversibilization done inside the host. It needs no full-group theory, K-theory or
  17.59.
- **The host is universal at the level of single elements.** A fixed fp simple group of
  type `F_∞` contains, as single elements, arbitrary reversible Minsky machines. Its
  word problem stays trivial, while the cycle structure of its elements is
  undecidable.
- **What this says about BH.** A BH embedding does not lack computational expressiveness
  in fp simple hosts: an element can already run the word-problem algorithm. The whole
  difficulty is turning that computation into a homomorphism, i.e. relations that hold
  identically. The dynamical properties of the element must not leak into the image
  subgroup.

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS

**Verdict: PASS.** The reduction is complete and correct. Its only external inputs are Kari–Ollinger
Theorems 3 and 6, used exactly as printed.

**Checked against sources.**
- **Kourovka Notebook**, arXiv:1401.0300v46 (1 Sep 2026), Problem 21.74 (S. Kohl), read verbatim.
  - The three parts quoted under Statement match the printed text word for word.
  - There is no asterisk, so the problem is unsolved in that issue.
  - Parts (b) and (c) are exactly what the Theorem answers.
- **Kari–Ollinger, MFCS 2008**, the PDF recorded in the artifact (md5 6d5a3e72…), pp. 419–424, read
  directly.
  - The machine model (p. 421–422) is the one used in (R1) and (R2):
    - no decrement at a zero counter;
    - determinism means the state and the test vector fix the rest;
    - the three reversed-instruction rules are as used.
  - Theorem 3 (p. 423) reads: "It is undecidable whether a given 2-RCM is periodic". Periodicity is
    defined only for complete systems, as "every configuration is periodic" (p. 420), and the proof
    sketch builds complete machines. So part 1 reduces from exactly this problem.
  - Theorem 6 (p. 423) makes it undecidable whether a given complete 3-RCM, or a given not
    necessarily complete 2-RCM, admits a periodic configuration. Part 2 uses the 2-RCM clause.

**Step-by-step checks.**
- **(R1).** The reverse of the instruction used at `x` applies at `y = G(x)` and returns `x`,
  for each of `φ ∈ {−,0,+}`. Determinism of `T^{-1}` makes that reverse action unique.
  Correct.
- **(R2).** The image of one instruction is a union of cells. `Halt` is a union of
  (state, pattern) sets. Correct.
- **Claim 1.** The three domains, and the three images, partition `X`, and `f` is injective on
  each piece. Along backward rays `e_11` strictly decreases, and only backward rays map into
  backward rays. Forward rays are absorbing, and `e_13` increases along them. So every finite
  cycle consists of configuration codes, on which `f = G`. Every configuration has a code. Correct.
- **Claim 2.** A residue mod `p^a` determines `min(e_p, a)`, including for negative `n`. The class
  `0(L)` does not meet `X`, since `X` consists of odd numbers. The data that fix membership and the
  formula (state, and counter cells `{0, 1, ≥2}`) are read mod `L`. Each denominator of `λ_c`
  divides both `L` and `n`, hence `c`. Correct.
- **`F_M`.** The families `{c(L)}`, `{2c(2L)}` and `{f(c(L))}` are pairwise disjoint, because
  `X` is odd, `2X` is even and `f` is a bijection. So `s_1` and `s_2` are involutions with the stated
  action.
  - `F_M` is `f` on `X` and a copy of `f^{-1}` on `2X`.
  - With the other composition convention it is `f^{-1}` on `X`, with the same cycles.
  - Parts 1 and 2 follow as written. Correct.
- **Filler.** `Y = Z ∖ (X ∪ 2X)` is a union of classes mod `2L`, hence mod `L′`. The required node's
  formula and its items 1 and 3 were checked (see the Referee section there). Correct.
- **Moduli.** All moduli are `L`, `2L`, `λ_c L`, `4L′` or `16L′`, all `{2,3,5,7,11,13}`-smooth. So
  the instances lie in `CT_P(Z)` with `P = {3,5,7,11,13}`. Correct.

**Notes** (none affects the verdict).
1. **Literature input.** Kari–Ollinger print proof sketches only ("Due to page constraints most
   proofs are short sketches of the main idea", p. 421).
   - Theorem 3 rests on their Theorem 1: Hooper 1966, via Morita's 2-RCM simulation.
   - The 2-RCM clause of Theorem 6 rests on a one-sentence claim that Morita's conversion from
     3 counters to 2 preserves periodic orbits.
   - For (c) that last step can be avoided. The complete-3-RCM clause has a fuller sketch, and the
     construction here codes a third counter by a new prime (say `17`, keeping `11` and `13` for
     the rays; see "More counters"). So (c) holds in `CT_{P ∪ {17}}(Z)` using only that clause.
   - Cite the result as "conditional on the published theorems of Kari–Ollinger", as the node does.
2. **Remark on 21.74(a).** The sentence "products of multiplicative class maps with odd multipliers"
   is loosely worded. Read it as "elements of CT(Z) all of whose affine pieces have odd numerator
   and denominator". Such elements preserve `{0(2), 1(2)}`, so they are yes-instances. The remark is
   not load-bearing.
3. **Priority** (searched 2026-09-18: class transpositions with decidability, and "21.74"). Nothing
   treats 21.74.
   - arXiv:2607.17477 solves Kourovka 21.8 only among the class-transposition problems, as its
     HTML confirms.
   - arXiv:2604.12553 is about horizontal class transpositions.
   - Boege, arXiv:1612.05136, concerns single recursive permutations, not this problem.

## Second referee (bh-ref-q11, 2026-09-19): PASS, conditional on Kari–Ollinger Theorems 3 and 6

**The problem text.** Kourovka Notebook arXiv:1401.0300v46, 21.74 (S. Kohl), read at source:
"Is it algorithmically decidable whether a given element g ∈ CT(Z) (a) permutes a nontrivial partition of Z into residue classes? (b) has only finite cycles? (c) has no finite cycles?"
- There is no comment and no asterisk. Parts (b) and (c) are exactly what the Theorem answers.

**The reduction, checked independently.**
- **Claim 1.** The three domains (`Conf ∖ Halt`, `Halt ∪` forward rays, backward rays) and their images (`Conf ∖ Init`, forward rays, backward rays `∪ Init`) each partition `X`, for each fixed sign and cofactor `w`. So `f` is a bijection.
- **Finite cycles.**
  - Backward rays are entered only from backward rays, with `e_11` decreasing, and forward rays are absorbing.
  - So every finite cycle lies in `Conf ∖ Halt`, where `f = G`. Every configuration has a code.
- **Claim 2.** Each denominator of `λ_c` (a power of `7^(s−t)`, or `3`, `5`, `11`) divides both `n` and `L`, hence `c`. With `0 ≤ c < L` and `λ_c > 0`, the class map `c + Lk ↦ λ_c c + λ_c L k` is canonical.
- **`F_M = s_2 s_1`.**
  - `c(L) ⊆ X` is odd and `2c(2L)` is even, and the `f(c(L))` partition `X`. So `s_1 = (n ↔ 2n)` and `s_2 = (2n ↔ f(n))` are products of disjoint class transpositions.
  - `F_M = f` on `X`, `2f^(−1)(·/2)` on `2X`, and the identity elsewhere.
- **Part 1.** If every configuration is periodic, then `Halt = Init = ∅` and all orbits are finite. Otherwise, by Claim 1, the code of a non-periodic configuration has an infinite orbit.
- **Part 2.** The conjugates `ψ_j` of `ψ` onto the classes `j(L′) ⊆ Y` are words in class transpositions: `τ_(r_1(m_1), r_2(m_2))` conjugates to `τ_((j+L′r_1)(L′m_1), (j+L′r_2)(L′m_2))`. They have no finite cycles, and they act as the identity on `X ∪ 2X`. So `H_M` has a finite cycle iff `f` does.

**The external input.** Kari–Ollinger's inputs rest on Morita, TCS 168 (1996).
- I read Morita's own restatement with proofs: *Theory of Reversible Computing* (Springer 2017), Ch. 9, Lemmas 9.3–9.7 and Thm 9.2, citing [15] = TCS 168. It was fetched via MSI and is stored at `gq/src/bh-ref-q11/morita-book-ch9.pdf`, md5 096f5ac6….
- This supports KO Theorem 1 and the complete-3-RCM clause of Theorem 6.
- The 2-RCM clause of Theorem 6 ("the 3→2 conversion preserves periodic orbits") is not visible in Morita's Lemma 9.7, which concerns Gödel-encoded start configurations only. So I agree with the first referee: (c) is safest via the complete-3-RCM clause with a third prime (`17`), i.e. in `CT_(P∪{17})(Z)`.
- (b) uses Theorem 3 as printed.

**Flag, per the coordinator.** The bh-free-58 hand-off `gq-bh-bh-free-58-kourovka-state-2026-09-19` lists 06eb299b0 correctly as **PASS** (e2b397604f). What is still **unreviewed** is `ct-z-orbit-transversal-dichotomy-is-collatz-hard` (7b84a747f).
- The PASSes of 06eb299b0 and bc9e6452b import its items 1–2 (`ν_(G_T)(N) = o(N)`; orbits of `G_T` correspond to 3x+1 components).
- It should be refereed next.

**Prior-solution check (bh-ref-q11, 2026-09-19).** None found. So this node is a new result, not an independent rediscovery.
- **Kourovka Notebook** arXiv:1401.0300v46 (1 Sep 2026, the latest edition). 21.73 and 21.74 (S. Kohl, 21st issue) have no asterisk and no comment. The Archive of Solved Problems does not list them.
- **arXiv.** All papers with "class transposition(s)" or "residue-class-wise" in the abstract: 2401.15642, 2409.13341, 2504.08595, 2604.12553 and 2607.17477 (which solves other Kourovka problems). None treats conjugacy, cycles or undecidability in `CT(Z)`.
- **Kohl's papers.**
  - Math. Z. 264 (2010) introduces `CT(Z)`.
  - J. Group Theory 20 (2017) gives the Collatz groups `G_C` and `G_T`.
  - The RCWA manual: its "respected partitions" and tameness are a different question.
  - None of these decides 21.73 or 21.74(b),(c).
- **Belk–Bleak–Matucci–Zaremsky.** Neither the survey (arXiv:2306.16356v3, full text searched) nor BBMZ mentions `CT(Z)` or RCWA groups.
- **The nearest precedents,** to be credited as analogues:
  - Salo (arXiv:2011.07827), conjugacy in `2V`;
  - Belk–Bleak (arXiv:1405.0982), undecidability results for `2V`;
  - Kari–Ollinger 2008 and Morita 1996 for the machine inputs.
