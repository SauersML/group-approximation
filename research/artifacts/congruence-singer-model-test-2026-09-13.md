# Model test: Singer pairs and the Hensel covering of congruence kernels

Lane `ex2-weak-sofic-affine-targets`, 2026-09-13. Script:
`research/artifacts/congruence-singer-model-test-2026-09-13.py`, run on MSI with `/usr/bin/python3.11`
(pure Python, a few seconds). It checks the following, from
`research/artifacts/congruence-relator-width-part1-hensel-2026-09-13.md`.

- **Part A (Lemmas 2.1 and 2.2), `p in {2, 3, 5, 7}`, `2 <= n <= 6`, excluding `(n, p) = (2, 2)`.**
  - `sigma_1` is the `(p-1)`-th power of the companion matrix of a primitive polynomial.
  - `sigma_2` is its conjugate by the transvection `1 + E_12` for `n >= 3`, and by a searched `s` for `n = 2`.
  - Checked: `det sigma_1 = 1`; `dim(C(sigma_1) ∩ C(sigma_2)) = 1`; the layer map `Lambda` has rank `n^2 - 1`.
  - Ablation: one Singer element gives rank `n^2 - n`, so two are needed.
- **Unipotent control, `p | n`.** For the regular unipotent `J` and its transpose `J^T`, at
  `(n, p) = (4, 2), (3, 3), (6, 2)`, the rank also came out full. The proof uses semisimple elements,
  so this is only an observation.
- **Part B (Lemma 3.1), by brute force.** Lifts `g_i` of the Singer pair are fixed. The script
  enumerates `K_1` and checks that `{[g_1, b_1][g_2, b_2] : b_i in K_1}` equals `K_1`, in `SL_3(Z/4)`,
  `SL_2(Z/9)`, `SL_2(Z/27)` (two layers) and `SL_2(Z/25)`.

## Output (verbatim)

```text
A n=3 p=2 det1=1 common-centralizer-dim=1 rank(two)=8 rank(one)=6 target=8 OK
A n=4 p=2 det1=1 common-centralizer-dim=1 rank(two)=15 rank(one)=12 target=15 OK
A n=5 p=2 det1=1 common-centralizer-dim=1 rank(two)=24 rank(one)=20 target=24 OK
A n=6 p=2 det1=1 common-centralizer-dim=1 rank(two)=35 rank(one)=30 target=35 OK
A n=2 p=3 det1=1 common-centralizer-dim=1 rank(two)=3 rank(one)=2 target=3 OK
A n=3 p=3 det1=1 common-centralizer-dim=1 rank(two)=8 rank(one)=6 target=8 OK
A n=4 p=3 det1=1 common-centralizer-dim=1 rank(two)=15 rank(one)=12 target=15 OK
A n=5 p=3 det1=1 common-centralizer-dim=1 rank(two)=24 rank(one)=20 target=24 OK
A n=6 p=3 det1=1 common-centralizer-dim=1 rank(two)=35 rank(one)=30 target=35 OK
A n=2 p=5 det1=1 common-centralizer-dim=1 rank(two)=3 rank(one)=2 target=3 OK
A n=3 p=5 det1=1 common-centralizer-dim=1 rank(two)=8 rank(one)=6 target=8 OK
A n=4 p=5 det1=1 common-centralizer-dim=1 rank(two)=15 rank(one)=12 target=15 OK
A n=5 p=5 det1=1 common-centralizer-dim=1 rank(two)=24 rank(one)=20 target=24 OK
A n=6 p=5 det1=1 common-centralizer-dim=1 rank(two)=35 rank(one)=30 target=35 OK
A n=2 p=7 det1=1 common-centralizer-dim=1 rank(two)=3 rank(one)=2 target=3 OK
A n=3 p=7 det1=1 common-centralizer-dim=1 rank(two)=8 rank(one)=6 target=8 OK
A n=4 p=7 det1=1 common-centralizer-dim=1 rank(two)=15 rank(one)=12 target=15 OK
A n=5 p=7 det1=1 common-centralizer-dim=1 rank(two)=24 rank(one)=20 target=24 OK
A n=6 p=7 det1=1 common-centralizer-dim=1 rank(two)=35 rank(one)=30 target=35 OK
A-unipotent n=4 p=2 common-centralizer-dim=1 rank(J,JT)=15 target=15
A-unipotent n=3 p=3 common-centralizer-dim=1 rank(J,JT)=8 target=8
A-unipotent n=6 p=2 common-centralizer-dim=1 rank(J,JT)=35 target=35
B SL_3(Z/4) |K_1|=256 |[g1,K1][g2,K1]|=256 |[g1,K1]|=64 OK
B SL_2(Z/9) |K_1|=27 |[g1,K1][g2,K1]|=27 |[g1,K1]|=9 OK
B SL_2(Z/27) |K_1|=729 |[g1,K1][g2,K1]|=729 |[g1,K1]|=81 OK
B SL_2(Z/25) |K_1|=125 |[g1,K1][g2,K1]|=125 |[g1,K1]|=25 OK
ALL OK
DONE
```

**What it does not check.** Case N of part 2 (the near-scalar matching and localization), and prime
powers `q` that are not prime.
