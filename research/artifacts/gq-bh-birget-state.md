# Lane bh-birget: state, 2026-09-19

Hand-off for whoever continues the Birget route. Every item cites a commit on main.

## Target

Birget's question, arXiv:math/0310335 §1, verbatim: "Is there some cap on the computational complexity of the
word problem of finitely presented simple groups?" The route aims at a **no-cap** answer.

Main node: `research/birget-question-via-decidable-bartholdi-mitrofanov-hosts.md`, latest version e83e0ac345.

## Established or refereed

1. **Transfer lemma.** A f.g. self-similar `G` whose relator kernel is a finitely generated lift ideal embeds in
   a finitely presented simple group. Zaremsky's proof reruns, because regrouping preserves lift ideals.
   2222dfd660; referee bh-ref-c PASS, ab22b01462.
2. **Reduction.** Birget "no cap" follows from (a) + (c) for one family: (a) a hard word problem, and (c) a
   finitely generated lift ideal. Solvability, formerly item (b), is automatic by Kuznetsov. Referee bh-ref-e,
   03514e0598.
3. **Bartholdi–Mitrofanov Proposition 2.4.** In arXiv v1 and v4 the printed proof has a gap, and `[g,u] ≠ 1`
   for every machine. Replacing `u` by a partner `p` supported on `0^*1A^ω` restores Proposition 2.4′ and
   Theorems A and A″ for `G′_M = ⟨Φ_M, p, p′⟩`.
   - Node `bartholdi-mitrofanov-proposition-2-4-gap-and-repair`, e83e0ac345; referee bh-ref-f PASS,
     6747a7e43d.
   - The published version was not checked, and the authors have not been contacted (the user's call).
4. **(a) holds for `G′_M`** once the machine uses Minsky's encoded input with a doubly exponential rescaling.
   bh-ref-e.
5. **Survival criterion.** Take a self-or-trivial recursion, or a weighted one where each section of a
   generator is itself, a lighter generator, or trivial. If every survival-graph loop group has a finitely
   presented image, then (c) holds. Referee bh-ref-f PASS, 6747a7e43d.
6. **(c) holds** for the calibration machine, for the increment loop `G_1` (loop images `D₁₂` and `Z`), for
   the repaired `G′_1` (loop images `Z/2 × D₁₂` and `Z`), and for the ternary core `Q`, where
   `N_Q = ⟨⟨b²⟩⟩_lift`. Referee bh-ref-f PASS, e733763d78 and 6747a7e43d.
7. **(c) fails** for Theorem A″'s universal machine, by Kuznetsov and the transfer lemma.

## The open crux

(c) for one **hard** machine in `G′_M`.

- **The counter rules, type IX (conditional decrement) in §2.1**, as quoted from the arXiv HTML:
  - `Φ(0,s_i) = (s_k, 𝐢₁)`;
  - `Φ(𝐢₁,x) = (s_k^(-1) s_j x, 𝐢₂)` and `Φ(𝐢₂,x) = (x^(-1) s_j^(-1) s_k x, 𝐢₁)`;
  - `y` passes `𝐢₁` and `𝐢₂`;
  - `Φ(𝐢₁, s_i) = (ε, 0)`.
- **The difficulty.** `x` has sections of length 3. So the recursion is not self-or-trivial, and weighted
  length can grow on a single `x`.
- **Why pairs are fine.** An `x²` has section `x` at `𝐢₁`, so it halves.
- **What is needed.** A potential that counts `x`-runs, not `x` letters, and that decreases except along
  finitely presented loop images.
- **Type I (increment)** gives `x|_(𝐢₁) = x²`, which doubles.
- **The first test** is an increment/decrement loop built from types I and IX; after it, a hard two-counter
  machine.

## Cautions

- Tests 1–2 were misread twice: the wall letter `1`, then `s_†` taken as finitary, a rule that belongs to §3.
  Read rules at source, e.g. bh-ref-f's MSI copy at `refs/bm1710/`, before trusting any recursion.
- §3 of Bartholdi–Mitrofanov (the order problem) was not checked.
