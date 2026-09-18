---
rg: 2
id: bmw-40-40-193-281-332-parity-kernels-not-left-orderable
kind: claim
title: For the BMW classes 40_40 #193, #281 and #332 the parity kernel is not left-orderable, witnessed by a 4-generated subgroup with an unsatisfiable positive-cone certificate
distinct_from:
  bmw-44-sat-survivor-parity-kernels-not-left-orderable: that is the dichotomy "reducible or non-left-orderable parity kernel" for the same three classes; this proves the second alternative unconditionally and so implies it
  bmw-degree-44-53-parity-kernels-not-left-orderable: that census theorem excludes exactly these three classes; together the two cover every class of degree (4,4) in the census that is not certified reducible
  bmw-40-40-281-is-irreducible: that proves #281 irreducible and says nothing about orders; with it, #281 is an irreducible lattice whose parity kernel is not left-orderable
  small-degree-irreducible-bmw-parity-kernels-not-left-orderable: that is the refutation by positive-cone SAT on letter balls; there these three classes stayed SAT
artifacts:
  - experiments/bmw-44-survivor-left-orders-2026-09-17/README.md
  - experiments/bmw-44-survivor-left-orders-2026-09-17/cert_193.json
  - experiments/bmw-44-survivor-left-orders-2026-09-17/cert_281.json
  - experiments/bmw-44-survivor-left-orders-2026-09-17/cert_332.json
  - experiments/bmw-44-survivor-left-orders-2026-09-17/verify_cert.py
  - experiments/bmw-44-survivor-left-orders-2026-09-17/verify.log
---

**ESTABLISHED (computer-verified certificate).** Proof: `bmw-40-40-193-281-332-subgroup-cone-certificate-proof`.

**Statement.** Let `Γ` be the BMW group of degree (4,4) in class `40_40#193`, `#281` or `#332` of
`experiments/bmw-census-left-orders-2026-09-17/census_40_40.json`. All eight letters are involutions. Let `Γ^+` be the
parity kernel: the index-4 subgroup of words with an even number of vertical and an even number of horizontal
letters. It is torsion-free.

Then `Γ^+` is not left-orderable. More precisely, `Γ^+` contains a non-left-orderable subgroup `M` with four
generators, `M = ⟨x, y, f x^{-1} f, g y^{-1} g⟩`:

| class | x | y | f | g |
|---|---|---|---|---|
| #281 | `v0 v1` | `h0 h1` | `v3` | `h3` |
| #332 | `v0 v1` | `h0 h1` | `v3` | `h3` |
| #193 | `v1 v3` | `h1 h2` | `v2` | `h3` |

**Consequences.**
- The dichotomy `bmw-44-sat-survivor-parity-kernels-not-left-orderable` holds for all three classes, with no
  information on reducibility needed.
- Together with `bmw-degree-44-53-parity-kernels-not-left-orderable`, it removes that theorem's three exceptions:
  every irreducible BMW lattice of degree (4,4) or (5,3) has a non-left-orderable parity kernel. The census theorem
  refutes the others with letter-ball certificates, and this claim handles the three survivors.
- By `bmw-40-40-281-is-irreducible`, `#281` is an irreducible lattice whose parity kernel is not left-orderable,
  with intransitive local action (`S_3` fixing a letter) on both trees. That puts it outside the scope of
  `irreducible-tree-product-lattices-are-not-left-orderable`, which needs 2-transitive boundary actions, and it
  still behaves as that claim predicts.
- Every subgroup of `Γ` that contains a conjugate of `M` is not left-orderable.

**The certificate.** `cert_<class>.json` lists:
- 333 elements of `Γ^+` in normal form;
- 420 relations `e_p e_q = e_c`, none with product 1.

The certificate is found in the ball of radius 4 in the generators of `M`. The letter balls of the earlier census
runs (radius 10) miss it: its elements have up to 14 letters, and often both factors of a relation have 6 or 8
letters. The positive-cone CNF of the certificate has 910 clauses on 490 variables and is unsatisfiable.
`verify_cert.py` checks it independently (see the proof node).

## Attempts

- (w5-107b, 2026-09-18) The search went through three stages.
  1. The Z²-kernel `N = A ⋈ B` of `Γ^+(#281)` gave the first UNSAT, on a subgroup `N_1`.
  2. That core was shrunk to a subgroup of `N_1` with four generators.
  3. The four generators were rewritten as the uniform shape above, and all 144 subgroups of that shape were
     searched in each class. #193 and #332 each have one UNSAT subgroup. The product class `#0`, which is
     left-orderable, has none (`gs0.log`).
- (w6-107c, 2026-09-18) **A hand proof with no SAT: `bmw-40-40-193-281-332-klein-chain-proof`.**
  - **Lemma.** In a left-ordered group, `a b a^{-1} = b^{-1}` with `b ≠ 1` forces `|b| < |a|`. So a
    cyclic chain in which each element inverts the previous one is impossible.
  - **The chain for #281 and #332.** `h0h2 → v3v0v2v3 → h3h1h2h3 → v1v2 → h0h2`, where each element
    inverts the one before it.
  - **The chain for #193.** `h0h1 → v0v3 → h3h0h2h3 → v2v0v1v2 → h0h1`.
  - **Why it holds.** Each of the four relations is a letter conjugate of one of two Klein pairs
    `pq ⇝ rs`. In such a pair, `p` centralizes `rs` and `q` swaps `r ↔ s`, and both are read off
    from the squares directly.
  - **Check.** `experiments/bmw-klein-chains-2026-09-17/verify_klein.py` re-checks all twelve
    relations by rewriting and logs the traces. The statement is therefore now established by a
    hand proof as well as by the certificate.
  - **Structure.** The certificate subgroup `M` is not needed. The obstruction is a cycle of
    order-of-magnitude comparisons between Klein-bottle subgroups.
