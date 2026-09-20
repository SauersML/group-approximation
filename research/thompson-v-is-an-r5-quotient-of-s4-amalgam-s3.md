---
rg: 2
id: thompson-v-is-an-r5-quotient-of-s4-amalgam-s3
kind: claim
title: Thompson's V is the quotient of S4 amalgamated with S3 by the single word r5
artifacts:
  - experiments/thompson-v-r5-cocycles-2026-09-17/prefix_cocycles.py
  - experiments/thompson-v-r5-cocycles-2026-09-17/nonabelian_covers.py
  - experiments/thompson-v-r5-cocycles-2026-09-17/twisted_triples.py
  - experiments/thompson-v-r5-cocycles-2026-09-17/low_index_r5.py
  - experiments/thompson-v-r5-cocycles-2026-09-17/rigid_triples.py
distinct_from:
  thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3: that kills all four long words r5..r8 and is established; this asks whether r5 alone already normally generates the kernel, so that r6, r7, r8 are consequences of r5 over the amalgam.
  bleak-quick-finite-presentations-of-thompson-v: that imports the relator lists as published; this is a question about redundancy inside the (2.4) list, which Bleak--Quick did not address for the three-generator version.
---

Let `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)` (right action) and
`G0 = <a, b, c | a^2, b^3, (ab)^4, c^2, (ac)^3> = S4 *_(C2) S3`. By
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, `V = G0/<<r5, r6, r7, r8>>`.

**Claim (OPEN).** `V = G0/<<r5>>`, where

```text
r5 = (cab^-1aba)^2 cb (cabab^-1a)^2.
```

If true, a finite action of `V` is exactly an `S4`-set and an `S3`-set on one set that agree on `a`
and fix one word of length 26, and the soficity form
`thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words` becomes a one-word statement.

## Decomposition

Write the Bleak--Quick (2.3) words as `R2 = c^(ac) a^-1`, `Rsplit`, `R4a`, `R4b`, `R5`
(transcribed in `experiments/nonsofic-certificates/presentations/verify_thompson_steinberg_presentation.py`,
`R_WORDS[3:]`). `R2` already holds in `G0` (`(ac)^3 = c^2 = 1` gives `c^(ac) = a`), so by
Bleak--Quick's theorem for (2.3), `V = G0/<<Rsplit, R4a, R4b, R5>>`. The claim therefore splits into
three prerequisites, each of which can fail independently:

- **P1.** `Rsplit in <<r5>>_G0` (the short word r5 is KBMAG's Tietze replacement of the split
  relation, but the replacement was made modulo all the other relators, so this is not automatic).
- **P2.** `R4a, R4b in <<Rsplit>>_G0` (disjoint-support commutation of S23-type swaps follows from the
  split relation over the amalgam).
- **P3.** `R5 in <<Rsplit, R4a, R4b>>_G0`.

P1 and P2 and P3 together give the claim. Reading the Bleak--Quick proof of (2.3) (source lines
856--930 and 1300--2072): every lemma before their equation `[23,23]` (line 1679) uses only R1--R3,
including the conjugation tables `23^23 = 22`, `22^12 = 23`, `23^12 = 23`, `23^23 = k01`,
`23^k01 = 23` and `[(kappa lambda0), (mu lambda1)] = 1`. R4 first enters at `[23,23]`
(commutation of disjoint S23 swaps with different labels) and R5 first at `[33,23]` (line 2072).
So P2 is exactly the question whether the `[23,23]` commutations follow from the rigid-swap
calculus that R1--R3 already produce.

## Attempts

All computations below are exact finite computations; a miss is inconclusive for the claim.

1. **Locally constant abelian covers (dead as a separating tool).** A depth-k voltage rule
   `phi_x(z[:k]) in Z/p` lifts `a, b, c` to the skew action on `C x Z/p`; a relator holds for the
   lift iff every cylinder loop form vanishes (`prefix_cocycles.py`).
   - Control: `G0` alone is separated from `r5`, `r8` for all tested `k`, and from `r6`, `r7` from
     `k = 4` on, so the method sees the amalgam-to-V gap.
   - `G0 + r5` versus `r6, r7, r8`: no separation for `k = 0..9`, `p = 2, 3, 5`; the base rank equals
     the rank with all eight relators, `2^(k+1)` out of `3 * 2^k` unknowns.
   - `G0 + Rsplit` versus `r5, R4a, R4b, R5, r6, r7, r8`: no separation for `k = 3, 5, 7`, `p = 2`.
   So once one long relator is imposed, this cover class cannot distinguish the quotient from V at
   any tested depth; it cannot decide P1, P2 or P3.
2. **Locally constant S3-fibre covers, depth 2** (`nonabelian_covers.py 2 3 ...`). `G0 + r5` has
   1296 lifted triples, none violating `Rsplit, R4a, R4b, R5, r6, r7, r8`. Control `G0` alone has
   lifts violating `r5`, `Rsplit` and `R4a`. Depth 2 with fibre size 4 was too slow without
   propagation and was stopped.
3. **Twisted triples in V** (`twisted_triples.py`). With `a'(00u) = 01 alpha(u)` and
   `c'(1u) = 00 psi(u)` for permutations `alpha, psi` of `{0,1}^d`, all 24 triples at `d = 2`
   (alpha = id) satisfy `G0 + r5` and every test relator, and all 576 triples (alpha, psi arbitrary)
   satisfy all eight relators, including the control run with base `G0` only. This family consists
   of images of V and has no separating power.
4. **Finite quotients (low-index subgroups).** V is infinite and simple, so a subgroup of index
   `2 <= n < infinity` in `G0/<<r5>>` would refute the claim outright. `low_index_r5.py` runs the
   Sims coset-table backtrack with full HLT deduction and re-verifies every table found as
   permutations.
   - `G0/<<r5>>` has **no subgroup of index `2..16`** (only the trivial table is found). Index 2 is
     also excluded by hand: `G0^ab = Z/2` generated by `a = c`, and r5 has odd total exponent 17 in
     `a, c`.
   - Controls: `G0` has 216 proper subgroups of index `<= 6`; `G0/<<r6>>` has subgroups of index
     2, 3, 4, 6, 8 (31 up to index 8); `G0/<<r7>>` has 37 up to index 10. `G0/<<r8>>` and
     `G0/<<Rsplit>>` have none up to index 10.
   So among the four long words, r6 and r7 alone certainly do not present V, while r5, r8 and
   Rsplit each pass the finite-quotient test to the tested index.
5. **Rigid triples in V** (`rigid_triples.py`). Triples with `<a, b>` rigid on the cones of a
   complete prefix code `P` and `<a, c>` rigid on a code `Q` (codes of word length `<= 3` and at most
   6 cones; 322680 triples satisfying `G0`): exactly 1064 also satisfy r5, and every one of those
   satisfies r6, r7, r8, Rsplit, R4a, R4b and R5. No homomorphism `G0/<<r5>> -> V` of this shape
   escapes V's relations.

The approach "find a finite, abelian-cover or small-V quotient of `G0/<<r5>>` in which r6 fails" is
recorded dead at these sizes. The evidence leans towards the claim, but none of it proves it.
Next falsifiable step: a Tietze derivation of `Rsplit` from `r5` over `G0` (P1), for example by
Knuth--Bendix on `G0 + r5` with `Rsplit` as the goal word, run in parallel with a search for a
larger non-rigid quotient (for example in `V_(3,1)` or `2V`) in which r5 holds and r6 fails.
