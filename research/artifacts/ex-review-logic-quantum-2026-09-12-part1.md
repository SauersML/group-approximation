# EX review, logic and quantum: part 1. RF_fp and LEF_fp are Pi^0_2-complete (ex-complexity-sofic)

Lane `ex-verify-logic-quantum`, 2026-09-13 00:40 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.
Landings: 076f1bec8c, 0f7c32377c (the artifact `rf-fp-pumped-minsky-part{1,2,3}-2026-09-12.md` and
eleven nodes) and ec53d79731 (the Lemma A input correction).  Sibling review: `ex-review-groups-2026-09-12-part3.md`
§3.2 (PASS after correction).  Its B4 check lists Lemma 4.14 and Theorem 4.3(b) as used without
re-reading.  The zero-case defect below lives exactly there.

## 1.0 Verdicts

| item | verdict |
|---|---|
| Lemma C, `clocked-search-machine-halts-universally-exactly-on-inf` (+ `-proof`) | PASS (agrees with §3.2) |
| Lemma A, `pumped-divergent-minsky-word-lies-in-profinite-kernel` (+ `-proof`) | Input slip `iota(c') = 1 - e_tau(c)`: found by ex-verify-groups, corrected in ec53d79731, PASS.  **GAP** (§1.4): Step 2 needs every zero semigroup word to have the same group word, which fails under KMS's displayed relations.  Corrected forward here to `G_0` |
| Lemma B, `pumped-halting-clocked-minsky-group-is-residually-finite` (+ `-proof`) | B1--B3 and the invariance of `F`: PASS.  **GAP** in B4 (§1.5): it needs `T -> T_1` injective.  Corrected forward to `G_0` |
| `kms-minsky-machine-groups-simulate-their-machines` (+ `-citation`) | **GAP.**  Clauses 4 and 5 are false at zero elements under G1--G8.  Corrected forward.  The quotes of Thm 4.3, Lemmas 4.4, 4.5, 4.14 match v5 verbatim |
| New `kms-group-with-stop-relations-simulates-all-words` (+ `-proof`) | The repair, authored here (§1.4) |
| `rf-fp-completeness-via-pumped-minsky-groups` into `residual-finiteness-of-finite-presentations-is-pi2-complete` | PASS after the corrections landed with this review |
| `lef-fp-completeness-from-rf-fp-completeness` into `lef-of-finite-presentations-is-pi2-complete` | PASS after the same corrections.  "f.p. LEF iff RF" is elementary; the Vershik--Gordon theorem number was not checked at source |
| Part 3 Corollaries 2--4 (inside `A_p^2 A`, semigroups, McKinsey) | PASS.  The semigroup corollary works in `S(P(M))` with `q_0 = 0` and needs no group import |
| Part 2 §5, the collapse of KMS's `S̃(M_n)` | PASS, checked on v5 p. 17 |
| Novelty, "no prior statement of (T0)" | Not rechecked (this session's web-search budget is exhausted).  It remains a bounded check |

**Sources read at source.**
- KMS arXiv:1204.6506v5, pp. 9--28 (PDF fetched on MSI).
- KMS, Bull. Math. Sci. 7 (2017) 309--352, doi:10.1007/s13373-017-0103-z, pp. 324--329.

## 1.1 Statement fidelity and the upper bound

- `RF_fp in Pi^0_2`: `for all w`, either `w = 1` (`Sigma^0_1`), or a finite `Q` and a map on
  generators kill every relator but not `w` (`Sigma^0_1`).  This is the finite-presentation clause
  of `rf-enumerated-pi3-completeness-proof`.
- `INF` is `Pi^0_2`-complete, and the map `e |-> ` presentation is computable.

## 1.2 Lemma C (the switch machine): PASS

- **Termination from any entry point and any register contents.**  Draining loops terminate.
  `LOOP` compiles over a fresh counter that only its own `while` decrements.  Sequencing preserves
  termination.
- **INF.**  After the first partial round, the rounds test `Phi(e, S_0 + t, N_0)`.  `Phi` is
  monotone in `s`.
- **FIN.**  The configuration at `L0` with `N = |W_e|` and all registers zero (so `tau = 0`)
  diverges.
- **Machine shape.**  Clocking inserts numbers that each carry one `Add(tau)`, so the machine stays
  simple and deterministic.
- **Note.**  KMS §2.2 (v5 p. 10) defines "universally halting" as "finitely many computations
  without repeated configurations".  The lane's term, "every forward computation is finite", is
  stronger.  It is defined in the node, and B1 needs it.

## 1.3 Lemma A, defect 1: the invariant at the input (corrected on main before this review)

`iota((c; 1, 0)) = 1 - e_tau(c)`.  Counterexample to the first statement:
- let `c_0 -> c` be an Add step on a divergent orbit;
- in `Sym(P(M))`, run that Add backward from `(c; 1, 0)` to `(c_0; 0, 0)`;
- the drain then fires, so the word is `0`.

I found this independently.  `ex-verify-groups` §3.2 found it first, and the lane corrected the
input to `pi = 1 + e_tau(c)` in ec53d79731.  The corrected Step 1 was re-derived: PASS.

## 1.4 Lemma A, defect 2: the zero case of KMS Theorem 4.3(b) (GAP, corrected forward)

**What Step 2 needs.**  Step 2 ends at the stop configuration `(0; e(d), 0, 0)`, where `d` depends
on `D`, hence on `phi`.  The step concludes that the group word of that zero semigroup element
equals `w(0; 0..0)`.  So it needs all zero elements of `S(P(M))` to have the same group word.

**KMS v5 does not give this.**
- **No stop relation.**  G1--G8 (pp. 19--20) contain no relation for `x_(q_0 ...)`.
- **A second model.**  The model `Ḡ` sets `z_(1,0) = 1` (p. 24, Lemma 4.9).  The same automorphism
  formulas over `S' = S(M)` minus the stop relation (3) also satisfy G1--G8:
  - G8 holds because the Minsky relations hold in `S'`;
  - G1--G7 do not involve (3).
- **Consequence.**  In that model `x_(q_0 A_0) * A_1 * ... * A_K` and
  `x_(q_0 A_0) * a_1 * A_1 * ... * A_K` are distinct basis vectors.  So in `G(M)` as displayed,
  distinct stop configurations have distinct words, and Thm 4.3(b) fails at zero.
- **Scope of the proof.**  Its proof (pp. 22--25) covers nonzero elements.  Even its parenthetical
  "in particular `α_i = β_i`" fails at zero, since `q_0 A_1 = 0 = q_0 A_2`.
- **The published version agrees.**  Bull. Math. Sci. §3.1 (p. 325) defines `S(MM_k)` with no stop
  relation and accept configuration `s_0 = (0; 0,...,0)`.  Remark 3.10 (p. 328) adds `q_0 = 0` only
  for a separate `S̃`.

As first written, Step 2 identifies `w(c')` with a `phi`-dependent stop word, which is not one
element of the profinite kernel.

**Repair**, landed as `kms-group-with-stop-relations-simulates-all-words` (+ `-proof`).  Put
`G_0(M) = G(M) + { x_(q_0 w) = 1 : w in U_0 }`: `2^(K+1)` relations, computable from `M`.

1. **Model.**  v5's `Ḡ` satisfies the new relations (`q_0 w = 0` in `S(M)`, `z_(i,0) = 1`).  So
   `G_0 -> Ḡ` is onto, and `G_0 in A_p^2 A cap ZN_(K+1) A`.
2. **Zero words die.**
   - Minsky relations keep partial configuration words partial, so a zero `q`-word reaches a
     `q_0`-word through Minsky relations.
   - G8 carries that chain into the group.  It ends at `x_(q_0 A_0) * (letters) = 1`, because
     `1 * a_i = 1` and `[1, A_i] = 1`.
   - So Thm 4.3(b) holds for `G_0`, zero elements included.
3. **Basis.**  `x_(i,w) = 1` whenever `w = 0`, so the convention `x_(i,0) = 1` of Lemmas 4.12 and
   4.15 is a relation.  The spanning half of Lemma 4.14 follows, and independence comes from `Ḡ`.
   So `T_0 ≅ T_1`.

**Step 2 with `G_0`.**
- The stop word is `1`, so `phi(w(c')) = 1` for every finite quotient `phi`.
- `w(c') != 1`, because its image in `Ḡ` is the basis vector of the nonzero element `w(c')`.

**The rest of Step 2, re-derived: PASS.**
- `f |-> f * a_pi` is an endomorphism of the abelian normal `T` (p. 20).  It induces `P̄` on
  `phi(T)`, with an idempotent power.
- The block `(*a_pi)^(tD+D)` is contiguous in the letter order of Thm 4.3(b).
- Pumps, unpumps and the drain are G8 relations.

## 1.5 Lemma B: B1--B3 and the invariance of F PASS; GAP in B4, corrected forward

Re-derived.
- **B1.**
  - Lemma 2.1 (v5 p. 10) uses only disjoint domains.
  - On partial configurations a Sub on `n` applies iff `l_n >= 1`, and a zero test iff `al_n = 1`
    and `l_n = 0`.
  - The forward part is a prefix of a halting computation.  A backward part has length
    `<= 2 l_tau + 1` by (C3).
  - So classes are finite.
- **B2.**
  - The projection to `M`, the `A`-letter set and `iota` are invariants.
  - The pump, lift, unpump argument is correct.
  - Zero-ness arises only through `q_0`.
- **B3.**
  - `I_R` is an ideal.
  - `S_fin` is finite.
  - The choices of `D` and `R` keep prescribed elements nonzero and distinct.
- **Invariance of `F`**, checked against formula (13) and pp. 23--24.
  - `a_j` and `a_j'` act through `z_(i',u)` and `z_(i,u a_j)`, the case fixed by `i_j` and by
    whether `u` contains `A_j`.
  - `ã_j` is trivial on `W_0`.  On `W` it acts as `a_j`, or through `z_(i, v a_j A_j)` for
    `u = v A_j`.
  - `A_j` acts by `z_(i,u) z_(i,u A_j)`, or trivially.
  - Inverses need no check: `T_1/F` is finite, and each letter induces a surjection of it, hence a
    bijection.
- The split extension is residually finite, and P. Hall applies to `G/T`.

**GAP.**  B4 writes `w in T` in the basis of `T_1` through Lemma 4.14.  For v5's displayed `G(M)`,
the map `T -> T_1` is not injective: `x_(q_0 A_0)` is nontrivial (the model over `S'`) but maps to
`1`.  With `G_0` it is an isomorphism (§1.4, item 3), and B4 holds as written.

## 1.6 The import node, the assembly and the corollaries

- **`kms-minsky-machine-groups-simulate-their-machines`.**  Clause 4 is now restricted to nonzero
  elements.  Clause 5 is restated as independence of the nonzero `x_(i,w)`.
  - The `-citation` route still says, of Lemma 4.14, "so `T -> T_1` is injective".  That is correct
    for `G_0`, not for `G`.  It is left to the owning lane.
- **Assembly.**  `e |-> G_0(P(M_e))` gives `INF <=_m RF_fp` and `FIN <=_m NONRF_fp`.
- **Corollary 2.**
  - `G_0` is a quotient of `G in A_p^2 A`, so it is solvable of derived length `<= 3`.
  - It is amenable, and TWW quasidiagonality makes it MF.
- **Corollary 3 (semigroups).**
  - INF: B3 separates `q`-elements.  Non-`q` elements admit only commutativity, so exponent bounds
    separate them.
  - FIN: Step 2 runs in any finite quotient semigroup, since some power of `a_pi` is idempotent.
- **Corollary 4 (McKinsey).**  Follows by definition of the algorithm.
- **Part 2 §5.**  KMS's `S̃(M_n)` kills every `q`-word carrying `A_(K+1) A_(K+2)`: pump once,
  idempotent reduction, unpump, drain (v5 p. 17).  The published version replaces that proof with
  the machine `MM_4` (pp. 328--329).

## 1.7 Forward corrections landed with this review

Merged into the current blobs and landed with `EX_ACK`:
- **The repair.**
  - New: `kms-group-with-stop-relations-simulates-all-words` and its `-proof`.
  - `kms-minsky-machine-groups-simulate-their-machines`: clauses 4--5 corrected.
- **The two lemmas and their routes.**
  - `pumped-divergent-minsky-word-lies-in-profinite-kernel` and its `-proof`: the group is `G_0`;
    the route requires the new claim.
  - `pumped-halting-clocked-minsky-group-is-residually-finite` and its `-proof`: the same.
- **The theorem.**
  - `rf-fp-completeness-via-pumped-minsky-groups`: the reduction map is `e |-> G_0(P(M_e))`.
  - `residual-finiteness-of-finite-presentations-is-pi2-complete`: the reduction is `G_0`, with a
    review-corrections paragraph.

**Left to the owning lane:**
- the artifact parts 1--3, where `G_0` should replace `G`;
- the last sentence of the Lemma 4.14 bullet in the import `-citation` route.
