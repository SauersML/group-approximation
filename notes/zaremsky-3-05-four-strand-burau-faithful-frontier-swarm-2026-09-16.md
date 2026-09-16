# Is Burau faithful on B_4? Frontier swarm lane, 2026-09-16

- **Lane:** `hi-fron-zaremsky-3-05-four-strand-bura` (FRONTIER angle).
- **Root:** `zaremsky-3-05-four-strand-burau-faithful`.
- **Hole worked (locked):** `brunnian-four-braids-admit-parity-correcting-push`.
- **Proof artifact:** `research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md`.
- **Scripts:** `experiments/zp-burau-parity-t-minus-one-2026-09-16/`.

## Angle

The root is open, and every live Yes route runs through the combinatorial core of
arXiv:2607.05283 (Bharathram–Birman–Brendle). The path is:

1. faithful on `B_4` iff faithful on `Brun_4` (established);
2. every nontrivial Brunnian braid has a five-strand Moody witness (open);
3. that witness comes from a "parity-correcting push" (open, Proposition 6.4 of the preprint).

The 2026-09-13 check had left step 3 as gap G1. The last step of the proposition asserts two
things without proof, and part 2 of that check observed that they contradict each other for a
kernel braid.

Frontier move: instead of trying to fill G1, ask what parity-clean counts can see at all. Answer:
only the Burau matrix at `t = −1`. That turns the observation "G1 is load-bearing" into an
explicit counterexample to the claim.

## State of the art as of 2026-09-16

- **arXiv:2607.05283** (Bharathram, Birman, Brendle).
  - v1 was submitted 2026-07-06 and checked on 2026-09-13 in lane z3-05-burau-search; verdict
    GAP (G1–G6).
  - The abstract page read 2026-09-16 shows v2, submitted 2026-09-14, with the comment
    "28 pages, 32 figures. Minor corrections and improved exposition". It is not withdrawn.
  - v2's HTML was seen only through the WebFetch summarizer. The corresponding statement appears
    to be Proposition 6.7, with the same enlargement of `γ_2` and the same unproved increase of
    `ι`. This is preliminary: numbering and hypotheses were not checked against the source.
- **Brendle–Margalit–Putman, arXiv:1211.4018** (v4 2014-06-30; Invent. Math. 200 (2015)
  263–310). Only the abstract was read, on 2026-09-16.
  - It identifies the kernel of Burau at `t = −1` with the hyperelliptic Torelli group, generated
    by twists about symmetric separating curves.
  - In braid form these are squares of twists about curves around an odd number of points. That
    wording was recalled, not checked against the paper.
  - Context only; nothing depends on it.
- **Artin's formula** for the half-twist action on `π_1(D_n)`: Birman 1974, Ch. 1, and
  Kassel–Turaev 2008, Ch. 1. Locators were not re-checked. It is classical, and it is the one
  imported input of the new direct proofs.
- No published solution to Zaremsky Problem 3.5 is known to this lane beyond the preprint above.

## What was proved

Details are in the artifact. All three direct proofs have `requires: []`.

1. **`moody-polynomial-change-certifies-burau-nonkernel-proof`** (Moody's criterion, artifact
   §§1–5).
   - There is an intersection form `I : H_1(D̃, P̃_*) → Z[t^{±1}]`.
   - The loop class of an arc satisfies `I = (1 − t^s) 𝕄`.
   - Mapping classes act on `H` through Burau, in every convention (transpose, mirror, `t ↦ 1/t`).
   - This closes the "Still to do" of that claim.
2. **`parity-clean-arc-counts-see-only-burau-mod-t-plus-one-proof`** (artifact §§6–7).
   - Theorem A holds modulo any ideal `𝔞` stable under `t ↦ 1/t`.
   - Parity lemma: parity holds iff `|𝕄(−1)| = |A ∩ α|` (winding identity plus signs).
   - Theorem B: if `ρ_n(Ψ) ≡ I mod (t+1)`, parity-clean representatives of `(β)ΨΓ` and `(β)Γ`
     cross `α` equally often.
3. **`burau-minus-one-kernel-meets-brunnian-four-braids-proof`** (artifact §8).
   - `Φ_0 = [(σ_1σ_2)^6, [A_14, [A_24, A_34]]]` (96 letters) is a nontrivial Brunnian braid with
     `ρ_4(Φ_0) ≡ I mod (t+1)` but `ρ_4(Φ_0) ≠ I`.
   - `ρ̄_4((σ_1σ_2)^6) = I` is checked by hand. The other facts come from exact arithmetic
     (`burau_minus_one.py`, all checks pass).
4. **Route `parity-correcting-push-fails-via-minus-one-kernel`** combines 2 and 3.
   - It establishes `parity-correcting-push-fails-for-a-brunnian-four-braid`, which is named in
     `refuted_by` of the hole.
   - Once established, the hole is REFUTED and the route
     `five-strand-moody-witness-via-parity-correction` is INVALIDATED.

## Approaches tried and where each dies

- **Fill G1 directly** (choose `γ''` so that parity survives and `ι` grows): dies for `Φ_0`, and for
  any braid in `Brun_4 ∩ ker ρ̄_4`, by Theorem B. No choice of `Γ ∈ B_5` can work, not only
  `Γ ∈ K_5`.
- **Replace `Φ` by powers or conjugates** (the repair of G6): dies too, since `ker ρ̄_4` is
  normal and closed under powers.
- **Use `Γ = 1` as a Moody witness for `Φ_0`**: it works as evidence (`moody_gamma_trivial.py`:
  `𝕄_{f(Φ_0)} ≠ 0 = 𝕄_1` in all 16 convention variants). But the change vanishes at `t = −1`, so
  it cannot come from parity-clean counts. The witness claim stays open.
- **Locate the false step of the preprint for `Φ_0`**: not done. It needs curve diagrams or
  Dynnikov coordinates for a 96-letter braid and its proper-product normal form.

## What to try next

1. **Pin the failing step.** Compute a proper-product form of a conjugate of `Φ_0`, run the
   Lemma 6.3 disk-type list, and follow the construction of Proposition 6.4 (v1) / 6.7 (v2). This
   shows whether Proposition 6.4, Lemma 6.3, Proposition 5.1, or the conjugation step fails. Then
   write it up as a precise erratum for the preprint's authors.
2. **Beyond `t = −1`.** A combinatorial Yes-proof must read more than `𝕄(−1)`. Candidates:
   - the span or extreme exponents of `𝕄`, via the heights `k_i` and uniquely attained extreme
     heights;
   - values at other roots of unity;
   - a Bigelow-style "no cancellation at the top degree" certificate.

   Test each on `Φ_0` and on `[T_c^2, Φ]` for small Brunnian `Φ`.
3. **Target the right subgroup.** Faithfulness on `B_4` is equivalent to injectivity of `ρ_4` on
   `Brun_4 ∩ ker ρ̄_4`.
   - Per the BMP abstract, `ker ρ̄_4` is generated by twist squares about odd curves; the
     braid-form wording is recalled, not checked.
   - A description of `Brun_4 ∩ ker ρ̄_4` in terms of those generators (for example, commutators
     `[T_c^2, Φ]`) would give a smaller target.
   - Once BMP has been read, state the reduction as its own claim.
4. **Review.** The three `requires: []` routes need independent review. The weakest step is the
   convention bookkeeping around Artin's formula (artifact §11, item 1).
