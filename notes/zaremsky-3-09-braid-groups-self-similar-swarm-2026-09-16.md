# Zaremsky 3.9, hole `some-fp-rf-group-acts-on-no-regular-rooted-tree` (swarm, 2026-09-16)

Agent `swarm-zaremsky-3-09-braid-groups-sel`. The hole was locked for this
session and is unlocked at the end.

## Setup

- **Root.** `zaremsky-3-09-braid-groups-self-similar`. Zaremsky, *Some open
  problems*, Section 3, Problem 9, added 5/18/24.
- **Hole.** Find a finitely presented residually finite group `G` with no
  faithful action on any rooted `d`-regular tree `T_d`. This is the second part
  of the problem.
  - Such a `G` refutes `every-fp-rf-group-embeds-in-fp-self-similar-group`,
    since self-similar groups are subgroups of some `Aut(T_d)` (Zaremsky,
    arXiv:2405.09722v2).
- **Classes.** `C_c` is the class of finite groups whose composition factors
  all have order at most `c`.
- **Equivalence.** For countable `G`, the following are equivalent.
  - `G` embeds in `Aut(T_d)` for some `d`.
  - `G` is residually `C_c` for some `c`.

  Proofs of the two directions:
  - Forward: the level-stabiliser quotients of `Aut(T_d)` are iterated wreath
    products of `S_d`, so they lie in `C_(d!)`.
  - Backward: Lemma E of the new artifact, §1. Refine a separating descending
    chain of normal subgroups to indices in `[2, c]`, build the coset tree, and
    embed it in `T_c`.
- **Profinite restatement.** Let `R_c(Ĝ)` be the intersection of the open normal
  subgroups `N` of `Ĝ` with `Ĝ/N` in `C_c`. Then:
  - a countable residually finite `G` fits in some `T_d` iff `G ∩ R_c(Ĝ) = 1`
    for some `c`;
  - a witness is a finitely presented residually finite `G` with
    `G ∩ R_c(Ĝ) != 1` for every `c`.

## What was proven

**New claim `finite-class-kms-groups-act-on-regular-rooted-trees`.** Status
computed ESTABLISHED by check.sh. Its route
`finite-class-kms-groups-act-on-regular-rooted-trees-proof` requires two
imported repo claims:
- `kms-minsky-machine-groups-simulate-their-machines`;
- `kms-group-with-stop-relations-simulates-all-words`.

The full proof is `research/artifacts/kms-groups-bounded-factors-2026-09-16.md`.

Statement:
- Let `M` be a Minsky machine and `p` a prime.
- Let `G_0(M)` be the KMS group of arXiv:1204.6506v5 §4.1, plus the `2^(K+1)`
  stop relations `x_(q_0 w) = 1`.
- Assume (FC): every nonzero `q`-element of `S(M)` has finitely many
  representative words.
- Then `G_0(M)` is residually (finite solvable with prime divisors in `pi(p)`).
  Here `pi(p) = {p} u primes(n_0(p)) u primes(q_p - 1)`.
- Hence `G_0(M)` acts faithfully on `T_(d(p))`, with `d(p) = max pi(p)`: on
  `T_7` for `p = 2` and on `T_3` for `p = 3`.
- ~~(FC) holds for every sym-universally halting `M`, by KMS v5 Lemma 3.5(a)
  plus a derivation argument. So the corrected groups behind KMS Theorems 4.17
  and 4.18 are not witnesses for the hole.~~ WITHDRAWN by the referee: KMS
  Lemma 3.5(a) is false as stated; see "Referee (2026-09-16)" below.

The mechanism:
1. `G_0 = T_0 x| B` with `B = prod_i B_i`, and `B_i ≅ F_p[s^±, (s-1)^-1] x| <s, s-1>`.
   This uses the BR lemma, KMS Lemma 4.1.
2. Elements outside `T_0` are separated by evaluating `s` at a point `ω` with
   `ω, ω - 1` units in `F_(q_p)`, and applying Krull.
3. On `T_0 ≅ T_1`, filter by the maximal `a`-weight `ν` of a representative
   word. This is finite by (FC).
   - Each `a`-letter is `D + N`: `D` preserves slices, and `N = S E_11` raises
     the weight.
   - `E_11 α^-1 E_11 = 0`, so the inverses have the same shape.
   - On graded pieces the letters act through the fixed block
     `α = [[1,-1,1],[1,1,0],[1,0,0]]` or `α - 1`. The characteristic polynomials
     are `x^3 - 2x^2 + x + 1` and `x^3 + x^2 + 1`.
   - Hence letter orders divide `n_0(p) p^e`.
4. The map `Φ_n(t b) = (φ(t) + E_n, ρ_n(b))` is a finite solvable quotient that
   separates `t` once `n` is large.

**Constants.**

| p | n_0(p) | pi(p) | d(p) |
|---|---|---|---|
| 2 | 7 | {2, 3, 7} | 7 |
| 3 | 8 | {2, 3} | 3 |
| 5 | 62 | {2, 5, 31} | 31 |
| 7 | 114 | {2, 3, 7, 19} | 19 |
| 11 | 60 | {2, 3, 5, 11} | 11 |
| 13 | 168 | {2, 3, 7, 13} | 13 |

**Experiment.** `experiments/kms-groups-bounded-factors-2026-09-16/`, about
40 s single-threaded; `output.txt` ends in `ALL CHECKS PASS`.
- It builds the KMS automorphisms on `T_1/E_n` for `(K, n, p)` in
  `(1,5,2), (1,5,3), (1,4,5), (2,3,2), (2,3,3)`, and for the one-command machine
  `q_1 = q_2 a_1`.
- It checks:
  - G1 for `H_1` and `H_2`, and G2;
  - the BR relation `A^(a^-1) A^-1 = A^((a')^-1)` of G3/G4, in KMS's convention
    `u^a = a^-1 u a`. The mirrored identity is a control and fails in every case;
  - the exponent bound `n_0(p) p^e` on generators and random words;
  - the prime-to-`p` parts of the generator orders.
- It is evidence only. The proof does not use it.

**Numbering corrections.** Theorem numbers were counted in the v5 LaTeX source,
and earlier drafts in this session were corrected against them:
- Theorem 2.6 = `t:MM`. Its part (d) gives sym-universally halting `MM_3`. This
  is not "Theorem 3.9(d)".
- Lemma 3.3 = `l:l9`, Lemma 3.5 = `l:fd`, Theorem 3.7 = `t:rc`.
- Lemma 4.1 = `lBRG`, Lemma 4.4 = `lH`, Theorem 4.17 = `t:rfg1`,
  Theorem 4.18 = `t:rfg`, Theorem 4.19 = `t:rhog`.
- Theorem 4.18 uses Theorem 4.17 through the machine of Theorem 3.7.
- The machines `M_n` of Theorem 4.19 are not covered.

**Attempts entry.** Attempt 3 was added to the hole node, recording where this
approach dies.

## Approaches and exactly where each dies

1. **Hard KMS groups as witnesses.**
   - *Idea.* They are finitely presented, residually finite and in `A_p^2 A`,
     with arbitrarily hard word problem. Nothing evident bounds the primes
     needed to separate elements.
   - *Dies for finite-class machines, by the new claim.* The primes are bounded
     by `pi(p)`, independent of `M`.
2. **`G(M)` as displayed, without stop relations.**
   - Here the basis group is not identified with `T_1`. The stop-relation claim
     shows the displayed relations do not kill stop words.
   - If `T(G(M))` were equivariantly the basis group of the model over `S(M)`
     without `q_0 = 0`, and (FC) held there, the same filtration would work.
   - Neither point was checked. **Open.**
3. **Pumped groups `G_0(P(M))`** of
   `pumped-halting-clocked-minsky-group-is-residually-finite`.
   - Their classes are infinite, because pumping trades `a_π a_ρ` freely. So `ν`
     is infinite and the filtration does not exist.
   - Heuristic, not checked. Their residual finiteness proof uses periodic
     quotients `a_π^D = a_π^(2D)`. On a periodic graded piece a letter is
     `α ⊗ 1 + E_11 ⊗ S`, with `S` a cyclic shift of period `D`.
     - If `D = p^k`, then `S` is unipotent in characteristic `p` and commutes
       with the letter. Filtering by the powers of `1 ⊗ (S - 1)` leaves
       `α + E_11`, whose characteristic polynomial is `x^3 - 3x^2 + 2x + 1`
       (Part A of the script). The analogous block comes from `α - 1`.
     - So bounded primes are expected again when `D` can be taken to be a power
       of `p`.
   - Whether the repo's proof allows `D = p^k`, and whether the other letters
     keep this shape, was not checked.
4. **Machines without (FC)**, including `M_n` of KMS Theorem 4.19. Not examined.
5. **Finitely presented metabelian groups.** Sketch, not refereed, and no
   literature search for priority.
   - *Claim.* Every finitely generated metabelian group `G` is residually `C_c`
     for some `c = c(G)`.
   - *Setup.* Let `M = G'` and `Q = G/G'`. By P. Hall, `M` is a finitely
     generated module over the Noetherian ring `R = Z[Q]`, so `Ass(M)` is
     finite. For each `P` in `Ass(M)`, fix a maximal ideal `m_P ⊇ P`, with
     finite residue field `F_(l^f)`.
   - *Elements of `M`.* For `v != 0` in `M`, `Ann(v) ⊆ P` for some `P` in
     `Ass(M)`.
     - By the Krull intersection theorem, `v ∈ ∩_j m_P^j M` would force
       `1 - a ∈ Ann(v) ⊆ m_P` for some `a ∈ m_P`, which is impossible. So
       `v ∉ m_P^j M` for some `j`.
     - `G` acts on the finite `l`-group `M/m_P^j M` through `(R/m_P^j)^*`,
       whose order has primes in `{l} u primes(l^f - 1)`. Let `C` be the
       centraliser.
     - `C` has finite index in `G/(m_P^j M)`. `M/m_P^j M` is central in `C`,
       and `C/(M/m_P^j M)` embeds in `Q`, so `C` is finitely generated
       nilpotent of class at most 2.
     - A finite quotient of `C` separating `v` projects onto its Sylow
       `l`-subgroup, where `v` survives because `v` has `l`-power order. Take
       the normal core of that kernel in `G/(m_P^j M)`; it has finitely many
       conjugates.
     - This gives a finite solvable quotient of `G` separating `v`, with primes
       in `{l} u primes(l^f - 1)`.
   - *Elements outside `M`.* They are separated through the finitely generated
     abelian group `Q`.
   - *Conclusion.* Baumslag's finitely presented metabelian groups are not
     witnesses: they act faithfully on regular rooted trees. The repo already
     has `baumslag-char-zero-metabelian-group-is-not-self-similar` for the
     stronger state-closed question.
   - *Why this does not extend to `A_p^2 A`.* The KMS basis group is a module
     over `F_p[B]` with `B` metabelian but not polycyclic, so its group ring is
     not Noetherian. The machine encoding lives exactly there. The general
     question stays open: is every finitely generated residually finite group in
     `A_p^2 A` residually `C_c` for some `c`?
6. **Linear groups.** Excluded by the hole node itself: finitely generated
   linear groups are virtually residually `p`.
7. **Products of large simple groups as profinite completions.** Attempt 2 of
   the hole node. The Kassabov--Nikolov frames are not finitely presented.

**Heuristic shape of a witness.** It must meet `R_c(Ĝ)` for every `c`.
- Inside solvable machine groups, this seems to need infinite semigroup classes
  together with a graded action whose eigenvalues have unboundedly many prime
  orders.
- Otherwise, it needs non-solvable finite quotients with unboundedly large
  simple sections that are needed for separation.

## Weakest points of the new claim, in the order a referee should attack

1. **The action of `ã_j'` on `A_0`-words.** It is read as the identity, which
   is forced by G5c.
2. **Imported structure.**
   - The exact block `α`, read off KMS formula `(ea)`, and the shape `D + N`
     from pp. 23--24.
   - The equivariant isomorphism `T_0 ≅ T_1` from
     `kms-group-with-stop-relations-simulates-all-words`.
3. **The derivation argument for (FC).** A nonzero `q`-free word only admits the
   commutativity relations `(ec)`, as in the proof of KMS Lemma 3.3.
4. **Lemma 2.1.** It uses that G1--G4 are the only relations among `L_1 u L_2`:
   every relation G5--G8 and every stop relation contains an `x`-letter.
5. **The experiment.** It covers only small models.

## Literature consulted (all read 2026-09-16)

- M. C. B. Zaremsky, *Some open problems*, PDF. Section 3, Problem 9 ("Added
  5/18/24") was read in this session's copy. The version date (July 12, 2026)
  and the URL come from the root node and were not re-checked against the copy.
- O. Kharlampovich, A. Myasnikov, M. Sapir, *Algorithmically complex residually
  finite groups*, arXiv:1204.6506v5 (2013-03-22). The LaTeX source was read:
  §2.6 (`t:MM`), §3 (`l:l9`, `l:del`, `l:fd`, `t:rc`), §4.1 relations G1--G8,
  Lemma 4.1 (`lBRG`), pp. 22--24 automorphism formulas, and the proof of
  Theorem 4.17.
- M. C. B. Zaremsky, *Embedding finitely presented self-similar groups into
  finitely presented simple groups*, arXiv:2405.09722v2. Only metadata was
  checked this session; the definition of self-similar is taken as quoted in
  the repo nodes.
- A. C. Dantas, T. M. G. Santos, S. N. Sidki, *Intransitive self-similar
  groups*, arXiv:2004.08941v2. Only metadata was checked this session; not
  used in any proof.
- M. Kassabov, N. Nikolov, *Cartesian products as profinite completions*,
  arXiv:math/0602446. As recorded in the hole node; not re-read.
- Krull intersection theorem, in its standard textbook form (Atiyah--Macdonald,
  Ch. 10). Used in Step 3 of the claim and in sketch 5 above. The exact
  corollary number was not re-checked.
- P. Hall, finite generation of `G'` as a `Z[G/G']`-module for finitely
  generated metabelian `G`. Classical; not re-fetched; only sketch 5 uses it.

## Files

- `research/finite-class-kms-groups-act-on-regular-rooted-trees.md` (claim)
- `research/finite-class-kms-groups-act-on-regular-rooted-trees-proof.md` (route)
- `research/artifacts/kms-groups-bounded-factors-2026-09-16.md` (full proof)
- `research/some-fp-rf-group-acts-on-no-regular-rooted-tree.md` (Attempts entry 3)
- `experiments/kms-groups-bounded-factors-2026-09-16/check_kms_bounded_factors.py`
  and `output.txt`

## Referee (2026-09-16)

Adversarial check of the lane's output before landing.

**Checked and accepted.**
- Theorem numbering against the v5 LaTeX source (one counter per section).
- G5--G8 and all stop relations contain `x`-letters, so `G_0 = T_0 x| B` with
  `B = <L_1 u L_2 | G1--G4>`.
- The block `(ea)` equals `α = [[1,-1,1],[1,1,0],[1,0,0]]`, and the formulas
  for `ã_j`. `det α = -1`, and `E_11 α^-1 E_11 = E_11 (α-1)^-1 E_11 = 0`.
- Lemma E, and condition (N1) of `every-fp-rf-group-embeds-in-fp-self-similar-group`:
  a solvable group with primes at most `d` is in `W_d`.
- Lemma 2.1 and the Krull step. `ω` and `ω - 1` are units in `F_(q_p)`, and a
  nonzero polynomial of degree `d` is not in `m^(d+1)`.
- The filtration `E_n` (invariant, of finite index under (FC)), orders on
  graded pieces, and `Φ_n`.
- The table of `n_0(p)`, `pi(p)`, `d(p)` for `p <= 13`, recomputed from the
  experiment output.
- Lemma 7.1, which is correct but not needed any more.
- `bin/cairn search --similar` shows no duplicate.

**Fatal error found (fixed by replacement).**  Clause 3 of the claim said that
(FC) holds for every sym-universally halting `M`, by KMS v5 Lemma 3.5(a), and
therefore for the machines behind KMS Theorems 4.17/4.18.  That lemma is false
as stated.  Counterexample, with `K = 2`:

```text
1; e_1 > 0 -> Sub(1); 1        q_1 a_1 = q_1
1; e_1 = 0 -> 2                q_1 A_1 = q_2 A_1
2; e_2 > 0 -> Sub(2); 1        q_2 a_2 = q_1
2; e_2 = 0 -> 0                q_2 A_2 = q_0 A_2
```

- `M` is deterministic and sym-universally halting.  The non-accepted
  components are `{(2;x,0), (0;x,0)}` and the singletons `(0;x,y)` with
  `y > 0`.
- `q_1 != 0` in `S(M)`, but `q_1 = q_1 a_1^x` for all `x`.  So `q_1` has
  infinitely many divisors and representatives.
- KMS Lemma 3.3 (`l:l9`) fails for `W = q_1`.  Its proof invokes property (c)
  of Theorem 2.6, which is specific to `MM_2`, `MM_3` and gives no bound on
  backward chains.
- The step "Since M is sym-universally halting, E is finite" in KMS's proof of
  Theorem 4.17 is unsupported for this `M`.
- Evidence script: `experiments/kms-groups-bounded-factors-2026-09-16/referee_fc_counterexample.py`,
  with output in `referee_output.txt`.

**Changes made.**
- Claim: clause 3 was replaced.
  - (FC) holds for simple deterministic clocked universally halting machines,
    by clause 1 of `pumped-halting-clocked-minsky-group-is-residually-finite`.
  - The counterexample above is recorded as the second half of clause 3.
- Claim: "Not covered" now lists the machines of KMS 4.17--4.19, and
  `distinct_from` was reworded.
- Route: `requires` gains `pumped-halting-clocked-minsky-group-is-residually-finite`,
  and Step 7 was rewritten.
- Artifact: the §0 addendum was corrected, with a correction note.  §7 was
  rewritten (source of (FC), counterexample, consequences for KMS).  §8 was
  updated.
- Hole node Attempts entry 3: sym-universally halting machines are no longer
  claimed as covered.  The KMS 4.17--4.19 machine groups are listed as
  unresolved.
- The "What was proven" bullet above is struck through.

**Not decided, flagged for later.**
- Whether the machines actually used by KMS for Theorems 4.17--4.19 (`MM_3`
  from Theorem 2.6(d), the `M_n` of Theorem 3.9) satisfy (FC).
- Whether Theorem 4.17 itself holds for the counterexample machine.
- The committed literature-import nodes resting on KMS Theorems 4.17/4.18
  (e.g. `kms-arbitrarily-hard-fp-rf-groups`) inherit this gap in KMS's proof.
  Nothing here refutes their statements, and they were not edited.
- The metabelian sketch earlier in these notes was not refereed.

**Verdict.**  Clauses 1--2 under (FC) accepted.  Clause 3 was false and has
been replaced by a correct source of (FC) plus the counterexample.  Landed with
fixes.
