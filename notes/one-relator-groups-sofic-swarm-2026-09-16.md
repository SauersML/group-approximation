# one-relator-groups-sofic: swarm lane notes (2026-09-16)

- **Target:** `one-relator-groups-sofic` (Pestov, Question 4.10).
- **Hole locked and worked:** `unpeelable-extreme-one-relator-groups-sofic`, still OPEN.
- **Outcome:** partial progress on an explicit finite family, together with a reusable certificate
  node.
- **Details:** `research/artifacts/or-length16-nonfree-residue-2026-09-16.md`.
- **Scripts:** `experiments/or-length16-nonfree-residue-2026-09-16/`.

## Setup

The hole's census (Attempt 5) leaves, at each relator length, the two-generator torsion-free
relators that no descent certificate closes.
- At length 15, all 30 residue classes are closed. Attempt 6 used virtual-fibring certificates and
  Attempt 8 used Linton graph certificates.
- At length 16, there are 211 residue classes (`census3_16.out`). The landed
  `length15-16-free-piece-residue-classes-hyperbolic-special` proves 70 of them hyperbolic and
  virtually special. The other 141 are `NONFREE`: the Magnus piece has no letter occurring once, in
  any basis tried.

## New nodes

1. `non-proper-power-one-relator-complexes-are-aspherical` and its route
   `non-proper-power-one-relator-complexes-aspherical-citation` (`requires: []`, import).
   - The Asphericity Theorem is pinned verbatim from the Linton–Nyberg-Brodda survey TeX
     (arXiv:2501.18306v1, lines 1636–1713).
   - The route proves that the presentation complex matches the survey's hypotheses. The attaching
     map is an immersion iff `w` is cyclically reduced, and `deg = 1` iff `w` is not a proper power.
   - The primary sources, Cockcroft 1954 and Lyndon 1950, were not read.
2. `virtual-fibring-collapse-certificate-gives-rf-sofic` and its route
   `virtual-fibring-collapse-certificate-proof`.
   - The certificate `(w, α, τ, c)` has conditions (V0)–(V3):
     - a transitive permutation representation on which `w` acts trivially;
     - a cocycle with gcd 1;
     - an edge-span bound;
     - explicit vertex and edge moves collapsing `X[0,S+1]` and `X[−1,S]` onto `X[0,S]`.
   - It proves that `G` has an index-`k` subgroup `F_n ⋊ Z`, with `n = 1 − χ(X[0,S])`, so `G` is
     RF and sofic. The proof steps:
     - moves are strong deformation retractions;
     - a translation lemma shows the two certified collapses give every window collapse;
     - so `X[0,S]` carries the homotopy type of the infinite cyclic cover;
     - Kochloukova (`n = 2`) makes the kernel free;
     - the landed RF mapping-torus theorem and passage to the finite-index overgroup finish.
   - It requires three nodes: the asphericity import, Kochloukova, and the mapping torus.
3. `length16-residue-classes-virtually-free-by-cyclic` and its route
   `length16-residue-virtual-fibring-certificates`.
   - 172 of the 211 length-16 residue classes are virtually free-by-cyclic, RF and sofic. They
     include all 107 classes covered by no Linton certificate, landed or transported.
   - `verify.py` (length-15 lane) and the independently written `recheck.py` (this lane) both accept
     all 172 certificates, with identical `k`, `S` and `n`.
   - `accounting.py` ties the words to the census.
   - Index distribution:

     | Index | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
     |---|---|---|---|---|---|---|---|
     | Classes | 140 | 5 | 7 | 5 | 12 | 1 | 2 |

   - Fibre ranks range from 3 to 79.

Every length-16 residue class now carries at least one certificate. 172 are landed sofic. The other
39 have only Linton graph certificates: 37 landed, and 2 through the unlanded primitive-piece
transport.

## Approaches tried and where each stopped

1. **Linton graph certificate transported to primitive Magnus pieces**
   (`pieces.py`, `primcert.py`, `calib.py`).
   - If `W_0` is primitive in `F(3)`, then `B_0 ≅ F(2)` by an explicit automorphism, and the HNN data
     transport.
   - 36 of the 141 pieces are primitive. They give 34 `PASS`, 1 `FAIL(alternating cycle)` and
     1 `PASS_HLOOP`.
   - The calibration on the 100 landed letter-once classes agrees 100/100.
   - **Stops at:** 105 non-primitive pieces, where `B_0` is not visibly free. It is also not landed:
     the transport soundness node is missing, and so is the Haglund–Wise chain from "hyperbolic
     and virtually special" to soficity.
2. **Other zero-exponent bases** `t ↦ t a^j`, `|j| ≤ 3` (`shiftcert.py`).
   - **Stops at:** all 749 images of the 107 open words are non-primitive or reproduce the same
     `FAIL`/`HLOOP`.
3. **Wider partial-positivity search** (`ppwide.py`): moves of `census.WH`, lengths up to 50.
   - **Stops at:** no partially positive image. All 107 components were exhausted, with 260–724
     nodes each. This is not a proof: the move set is not the full Whitehead set.
4. **Virtual-fibring collapse certificates** (`vfib.py` search, two checkers).
   - **Result:** all 107 open words are certified, at index 2 (102), 4 (3), 5 (1) and 6 (1). So
     are 32 of the 34 transported-`PASS` words and 33 of the 70 landed-`PASS` words.
   - **Stops at:** 39 words have no certificate for index `k ≤ 8`, within `vfib.py`'s bounds:
     character coefficients `≤ 2`, potentials in `[−1, 1]` and a greedy collapse.
   - Six of the 39 time out at `k = 8` under a 13 s budget per word.
   - The absence of a certificate is not evidence against virtual fibring.
5. **Bieri vs Kochloukova.** The length-15 artifact cited Bieri's theorem without a node. This lane
   routes the kernel-freeness through the landed Kochloukova `n = 2` consequence instead, after
   checking that its hypotheses hold:
   - a finite 2-dimensional `K(H,1)` with `χ = 0`;
   - a surjection onto `Z` with finitely generated kernel.

## What remains open

- `unpeelable-extreme-one-relator-groups-sofic` covers every length. A finite census can only settle
  explicit lists.
- **Named next step.** A theorem-level argument that every relator in the residue family has a
  collapse certificate or a Linton certificate would be needed. Alternatively, work towards Wise's
  conjecture (hyperbolic one-relator groups are virtually free-by-cyclic) for this family.
- **The 39 Linton-only classes.** Landing soficity needs one route: the Linton claim, plus
  hyperbolic virtually special implies RF (the landed `hyperbolic-cubulated-groups-are-residually-finite`
  after passing to the cubulated finite-index subgroup), plus RF passing to finite-index overgroups.
- **Referee checks for the certificate claim.**
  - Attack the asphericity import: the primaries were not read.
  - Read `recheck.py`, about 230 lines, against (V0)–(V3).

## Literature consulted (2026-09-16)

**Read.**
- M. Linton and C.-F. Nyberg-Brodda, *The theory of one-relator groups: history and recent
  progress*, arXiv:2501.18306v1 (TeX source).
- M. Linton, *One-relator hierarchies*, arXiv:2202.11324v3.

**Checked for overlap.** None settles Pestov 4.10 or these relators.
- Berlai, arXiv:2502.05064.
- Wang–Zhang, arXiv:2607.21493.
- Fournier-Facio, arXiv:2608.02025.
- aimath.robertj1.com (problem index).
- An arXiv API search.

**Cited, not read.**
- W. H. Cockcroft, Proc. London Math. Soc. (3) 4 (1954) 375–384.
- R. C. Lyndon, Ann. of Math. (2) 52 (1950) 650–665.

**Repository imports.** Kochloukova (2006), via `kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop`.

## Referee (2026-09-16)

**Checked.**
- **Files.** I read every listed file. The only unlisted files in the lane are these referee
  additions.
- **Asphericity import.**
  - I downloaded the arXiv e-print of 2501.18306v1 again. The pinned statements match `main.tex`
    word for word (lines 1636–1713), and the Cockcroft and Lyndon entries match `main.bbl`.
  - Hypothesis matching is sound: an immersion is the same as a cyclically reduced relator, and
    degree 1 is the same as not a proper power.
  - Cockcroft and Lyndon themselves were still not read, and the route says so.
- **`virtual-fibring-collapse-certificate-proof`.** I read Steps 0–11 against the three imports:
  asphericity, Kochloukova `n = 2`, and RF of mapping tori of finitely generated RF groups. I found
  no gap. The steps covered:
  - the `K(H,1)` with `χ = 0`;
  - the translation lemma, so the window is a finite `K(N,1)`;
  - the Kochloukova hypotheses;
  - `N` free of rank `1 − χ(X[0,S])`;
  - `H ≅ F_n ⋊ Z`, then RF passing to `G` through a normal core.
- **`recheck.py`.** I read it line by line against (V0)–(V3). The review covered:
  - the right action;
  - tail heights on backward letters;
  - the window cell ranges;
  - edge multiplicity counted in both orientations;
  - loops excluded;
  - the end state must equal `X[0,S]`.
  No defect was found.
- **Third checker.** I wrote `referee_check.py` from the claim statement alone.
  - It accepts all 172 certificates with the same `k`, `S` and `n`.
  - Over `F_1000003`, `H_1(X[0,S]) = n` and `H_2 = 0` on every one.
  - It gives the same verdicts as `recheck.py` on the 9 controls.
- **Bulk negative control.**
  - For the 166 census words whose index-1 character has a non-monic Alexander polynomial, I took
    `±φ`, giving 332 lines. Such characters cannot be fibred.
  - Both `recheck.py` and `referee_check.py` reject all 332.
- **Reproduction.** Rerunning `verify.py`, `recheck.py` and `accounting.py` reproduced
  `verify*.out`, `recheck16.out`, `recheck_controls.out` and `accounting.out` byte for byte. I
  checked the artifact §2 table against my checker (172 rows, 0 mismatches) and the §3 list of 39
  words.
- **Status.** An arXiv search on 2026-09-16 found no general resolution of soficity for one-relator
  groups. The claim settles only an explicit finite list. Every claim id is at most 58 characters.

**Changed.**
- **`length16-residue-classes-virtually-free-by-cyclic`.** The old title said "all 107 without a
  Linton certificate". That misleads: none of the 141 `NONFREE` words has a *landed* Linton
  certificate, and 139 of them are in the claim. The title now reads "139 of the 141 with no landed
  Linton certificate", and a paragraph names the two words left out.
- **Referee records.** I recorded the referee check in:
  - `length16-residue-virtual-fibring-certificates`, together with the artifacts list;
  - the citation route (the verbatim-pin check);
  - the artifact, in §5 (commands and results).

**Verdict.** Landed with fixes. The certificate theorem and the 172-word claim are sound, given
the three imports. The weakest import is the asphericity theorem, taken from a secondary survey.
It is classical and correctly matched, but the primaries were not read.
