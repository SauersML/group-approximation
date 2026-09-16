# Zaremsky 2.13 swarm lane, 2026-09-16: full-twist-invisible characters of bF_{n,r}

- **Target:** `zaremsky-2-13-bnsr-of-pure-braided-bht-groups`.
- **Hole locked and worked:** `bf-n-r-twist-invisible-braid-characters-in-sigma-infinity`.
- **Outcome:** reduction plus partial results. The hole stays open.
- **Main file:** artifact `research/artifacts/zp-bf-n-r-twist-invisible-quotient-and-resonance-2026-09-16.md`.

## Setup

`bF_{n,r} = N ⋊ F_{n,r}`, `d = n - 1`. `Hom(bF, R) = pi^* Hom(F, R) ⊕ W` with `dim W = n(n-1)`. `W_0 ⊆ W` is
the full-twist-invisible subspace, `tau_phi ≡ 0`, of dimension `n(n-1) - 2`. The hole asks that
`[pi^* psi + phi]` lie in `Sigma^infinity` for `phi` in `W_0 \ {0}`, `n >= 3`. Part 2, Lemma 5 reduces this to
`[Phi_k]` in `Sigma^j(PB_k)` for large `k`, where `Phi_k(A_{ij}) = phi(type(i, j, k))`.

## What was established (proofs in the artifact)

1. **First-leaf quotient (Prop. 1, Lemma 2').**
   - `m(T, b, T) = sum_{j>=2} omega_{1j}(b) 1_{I_j}` defines a surjection
     `Psi: bF_{n,r} -> Z wr_Omega F_{n,r}`, with `Omega = Z[1/n] ∩ (0, r)`.
   - The `F_{n,r}`-orbits on `Omega` are the residue classes mod `d`, all infinite.
2. **First- and last-leaf characters (Props. 2, 2').**
   - The pullbacks of lamp characters are exactly the `phi` in `W` with `PPP = PPE = PEP = 0` (dimension `d`),
     and `tau = c(1)`. The `W_0`-part has dimension `d - 1`.
   - The last-leaf analogue gives a second `(d-1)`-dimensional part, independent of the first.
3. **Correction to the caution on the hole (Prop. 3).**
   - `Z wr_Omega F_{n,r}` is finitely presented. This uses Cornulier's criterion, as quoted by Mendonça: finitely
     many orbits on `Omega^2`, stabilizers `F_{[0,x]} × F_{[x,r]}`.
   - Every lamp character lies in `Sigma^2` of the quotient (Mendonça, arXiv:1709.06303, Theorem B, checked).
   - So the `Z wr Z` analogy on the hole does not apply.
   - Membership does not lift to `bF` in any case. The natural lift `D_x` of `e_x` is not a splitting
     (`PB_3 / Z ≅ F_2`). Whether `Psi` splits is open, and the caution's "non-split" is unverified.
4. **Mirror symmetry (Prop. 4).**
   - Complex conjugation gives an automorphism of `bF_{n,r}` with `pi^* psi + phi -> pi^* psi - phi`.
   - Corollary: for rational `phi` in `W_0`, `ker phi` is `F_m` iff `[phi]` is in `Sigma^m`. This uses the
     Bieri–Renz/Renz kernel criterion, which is standard and was not re-fetched.
5. **Depth bound (Prop. 5).**
   - A first-leaf restriction with support size `s >= 2 floor((k-2)/d)` lies only in pencil families of depth
     `>= s/2`, and depth `s/2` is attained.
   - With the pencil-depth upper bound and the resonance conjecture this would give `Sigma^infinity` on that
     subspace.
   - Unconditionally the sunflower obstruction gives `[Phi_k] ∉ Sigma^{s-1}(P_k)`, so no fixed `k` suffices.
6. **Interval twists (Prop. 6).**
   - For `phi` in `W_0`, every interval of `td + 1` consecutive strands has `sum Phi_k(A_{pq}) = 0` (cabling in
     `H_1`).
   - Consequence: the Yuzvinsky-type nonresonance theorems, which need nonzero weights on dense edges or on the
     dense edges at a hyperplane at infinity, cannot apply to any `phi` in `W_0`.

**New graph nodes.**

- Claim `bf-n-r-twist-invisible-restrictions-nonresonant` (open): eventual non-resonance of `Phi_k` in every
  degree.
- Route `bf-n-r-twist-invisible-via-braid-resonance` into the hole. It requires that claim,
  `pure-braid-bnsr-complements-are-real-resonance-varieties` (open) and
  `pure-braided-bht-braid-characters-dimension-n-n-minus-1`, and uses Lemma 5 of part 2.

## Computation (evidence; certificate boundary in artifact §7)

- **Scripts:** `experiments/zp-bf-n-r-first-leaf-star-resonance-2026-09-16/`.
  - `os_resonance_bf.py [main|deep]` computes Orlik–Solomon nbc normal forms and Aomoto ranks mod `2^31 - 1` and
    `10^9 + 7`.
  - `dense_edge_sums.py` computes the zero-weight subsets.
  - All sanity checks pass: Stirling dimensions, `d^2 = 0`, known circles, agreement with the repo's older code,
    the cabling relations, and `tau = 0` on `W_0`.
- **Certificate boundary.** `H^i = 0` mod `p` implies `H^i = 0` over `Q`, so those entries are certificates. A
  nonzero value is evidence only.
- **Results.**
  - For `n = 3, 4` and `k <= 9`, first-leaf characters have first resonant degree `s/2` with dimension `(s/2)!`.
  - Random `W_0` points and the part-2 example with `r` odd are acyclic below the top degree `k - 2`.
  - The part-2 example with `r` even is resonant in degree 1 at `k = 4` and degree 2 at `k = 6`, and has
    `H^{<=3} = 0` at `k = 8`.
  - No bounded resonant degree appears.
- **Zero-weight subsets.** For `n = 4` and `k <= 12`, the subsets with weight zero at every sampled `W_0` point
  are exactly the intervals of length `≡ 1 mod d`. For `n = 3` there are extra non-interval ones from `k = 10`
  (`r = 2`) and `k = 11` (`r = 1`). They vanish identically on `W_0`, since the samples span it (referee
  correction; the earlier text said "coincidental ones once `k >= 11`").

## Approaches and where each dies

- **Quotient transfer through `Psi`.** It gives nothing without a splitting. Even a split quotient transfers only
  holes, and the quotient has none at `m <= 2`.
- **Central-element criterion.** `Phi_k` kills the full twist, the only central element of `PB_k`.
- **Nonresonance vanishing theorems.** Their weight hypotheses fail identically on `W_0` (Prop. 6).
- **Fibration `P_k = F_{k-1} ⋊ P_{k-1}`.** The restriction to the free fibre never lies in `Sigma^1(F_{k-1})`,
  which is empty for `k >= 3`.
- **Resonance route.** Recorded as the new route. It needs two open inputs: the RS conjecture for `P_k`, and
  eventual non-resonance.
  - Prop. 5 settles the combinatorial side for first-leaf characters, provided the pencil-depth formula holds.
  - For general `phi` in `W_0` the pencil families containing `Phi_k` are not analysed.

## Literature gate (2026-09-16)

- **Checked directly.**
  - Zaremsky, open problems list (https://zaremsky.github.io/open_problems.pdf, version dated July 12, 2026):
    Problem 2.13 is still posed; no resolution is recorded.
  - arXiv author listing for Zaremsky (arxiv.org/a/zaremsky_m_1): no 2024–2026 paper computing
    `Sigma^m(bF_{n,r})` found.
  - L. A. de Mendonça, arXiv:1709.06303, PDF text: Theorem B, and the quote of Cornulier's finite-presentation
    criterion in §6.
  - D. C. Cohen, A. Dimca, P. Orlik, arXiv:math/0210409: abstract only (vanishing for local systems). The precise
    hypotheses of the Yuzvinsky-type theorems were not re-read. Prop. 6 kills both usual forms of the weight
    hypothesis, so the conclusion does not depend on which form is used.
- **Used as quoted in the repo, not re-fetched.**
  - Skipper–Wu arXiv:2103.14589;
  - Zaremsky arXiv:1803.02717, 1502.02620, 1507.08597;
  - Zaremsky arXiv:1403.8132 (BNSR invariants of `F_br`);
  - Koban–McCammond–Meier arXiv:1306.4046 (`Sigma^1(P_n)`).
- **Unverified, cited as such.**
  - Cornulier, Geom. Dedicata 122 (2006), known only through Mendonça's quote;
  - Bieri–Renz 1988 and Renz's kernel criterion;
  - Brown 1987 on finite presentation of `F_{n,r}`.

## Housekeeping

- An earlier import created a `__pycache__` directory in the experiment folder. It was deleted, and both scripts
  now set `sys.dont_write_bytecode = True`.
- Nothing was committed.

## Referee (2026-09-16)

**What was checked.**

- **Files.** All solver files were read in full: the artifact, both new nodes, these notes and the experiment
  folder. The referenced nodes were read with `bin/cairn context`. No unlisted solver files were found.
- **Proofs.** Every proof was checked by hand: Prop. 1 (equivariance, invariance under expansion, surjectivity),
  Lemma 2', Props. 2 and 2' (data, `tau = c(1)` and `tau = c'(r-1)`, intersection is the EPE line), Prop. 3 (orbits
  on `Omega` and `Omega^2`, stabilizers), Prop. 4 (conjugation commutes with blackboard cabling), Corollary 4.1,
  Prop. 5 (edge count `2(v-2)`, `v-1 <= 4(v-3)`) and Prop. 6 (the expansion identity `tau(k') = tau(k) - w(S)`).
  No mathematical error was found.
- **Citations.**
  - Mendonça arXiv:1709.06303v2: the PDF was downloaded and its text extracted. Theorem B, `|T| >= 3` gives
    `Sigma^2`, is quoted accurately. So is the §6 quote of Cornulier's criterion.
  - Cohen–Dimca–Orlik arXiv:math/0210409: the abstract page was fetched, and the title and journal reference are
    confirmed.
- **Independent recomputation.**
  - Script `scratchpad/ref213/indep.py`: an exterior algebra modulo the Arnold relations, ranks mod 32003, not
    nbc-based, with characters rebuilt from the type data.
  - It reproduces the Stirling dimensions for `k = 4, 5, 6` and every table row with `k <= 6`:
    - part-2 example: `r` odd, `k = 5`; `r` even, `k = 4, 6`;
    - first-leaf characters, `n = 3`: `r = 1`, `k = 5`; `r = 2`, `k = 4, 6`;
    - first-leaf characters, `n = 4`: `c = (1,0,0)` with `r = 2, 3`, and `c = (0,0,1)` with `r = 3`.
- **JSON.** The JSON outputs match the artifact table.
- **Discipline.** `bin/cairn search --similar` found no duplicates. The ids have 47 and 42 characters. The new
  claim has `## Attempts`. The route's `requires:` names the open claims it needs.

**What changed.**

- **Artifact §6, zero-weight subsets.**
  - The sentence "further coincidental subsets once `k >= 11`" for `n = 3` was wrong. Non-interval zero-weight
    subsets appear from `k = 10` for `r = 2` (e.g. `{2,4,6,9}`, `{2,5,7,9}`) and from `k = 11` for `r = 1`.
  - The 4 sampled points span `W_0` (dimension 4), so these subsets vanish identically; they are not coincidental.
  - Corrected in the artifact and in these notes. A note was added that the JSON lists are truncated at 20 entries.
- **Artifact §6, caveat.** A caveat was added that the Yuzvinsky/Cohen–Dimca–Orlik hypotheses were not re-read, and
  the CDO reference was added.
- **New claim.** The wording was softened. The nonvanishing at `s/2`, and the degree-1 and degree-2 resonance of the
  part-2 example, are mod-`p` evidence, not certificates. That `K` depends on `j` is proved separately by the
  sunflower argument.
- **Hole.** Not edited. Its caution about `Z wr Z` and `Sigma^2` is superseded at quotient level by Prop. 3, as the
  route's notes record. Whether the quotient splits remains unverified.

**Verdict.** The reduction and partial results are sound, and land with the small fixes above. The hole stays
open. The route needs two open inputs: eventual non-resonance, and the RS conjecture for `P_k`.
