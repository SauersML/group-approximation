# Kourovka candidates for new lanes (lane bh-kourovka-scout, 2026-09-19)

**Source and scope.**
- **Read at source:** Kourovka Notebook arXiv:1401.0300v46 (1 September 2026), pages 146–189,
  i.e. the whole 20th issue and the whole 21st issue. The local copy is
  `gq/src/bh-ref-kourovka-a/kourovka-1401.0300.pdf`.
- **Earlier issues:** scanned on 09-18 by bh-kourovka (`gq-bh-bh-kourovka-problems.md`) and
  not re-scanned here.
- **Checks.** For each problem below, main was searched with `git grep` on `research/` for an
  existing node. The arXiv checks are noted per item.

## Result of this lane

| No. | Problem | Result |
|---|---|---|
| 20.33 (A. Bauer, via J. Grochow) | Relativized Higman embedding theorem: a universal f.g. `G_X` for every oracle `X` | **Yes**, as a literature answer via Ziegler's generalized Higman embedding theorem (Scott arXiv:2404.11524v1, Thm 5.2.2, citing Ziegler 1980 Thm II.3.10). Node `kourovka-20-33-higman-relativizes-by-ziegler`; the deduction is a lane proof, not reviewed. |

## Ranked candidates (no node on main unless stated)

1. **21.119 (E. Schesler).** Is there a group `G` with finite-index subgroups `G_n` and maps
   `f_n : G_n → ℤ` whose kernels are of type `F_n` but not `F_{n+1}`?
   - **Constraints.** Every `G_n` is then `F_n`, so `G` is `F_∞`.
   - **Expected obstruction (not checked at source).** Finite cohomological dimension should
     cap the finiteness length of such kernels, via Bieri's theorems on normal subgroups with
     quotient ℤ. So `G` needs infinite cd, or torsion.
   - **Test groups.** `F_∞` groups of infinite cd with many virtual characters, attacked with
     the Witzel–Zaremsky Morse method for Σ^m, the same machinery as the T0 proof.
   - Not in main.
2. **20.47 (A. Le Boudec, N. Matte Bon).** Is every faithful, minimal, strongly proximal
   `F_n`-action on a compact space topologically free?
   - **Lane observation (unreviewed): yes when the action is extremely proximal.**
     - Suppose `g ≠ 1` fixes an open `U` pointwise.
     - Push `supp(g)` into `U` by some `h`. Then `k = hgh⁻¹` has support inside `Fix(g)`, so
       `k` commutes with `g`.
     - In `F_n`, maximal cyclic subgroups are malnormal, which puts `h` in the maximal cyclic subgroup containing `g`, so `k = g` and
       `supp(g) ⊆ Fix(g)`, a contradiction.
   - So a counterexample must be strongly proximal but not extremely proximal. This is
     probably known to the proposers.
   - Related to the (RA) work: topologically free versus free, bh-ra-*.
3. **21.44 (S. Eberhard).** Does the infinite iterated wreath product of `A_5` contain a
   finitely generated dense subgroup of subexponential growth?
   - A web search summary says arXiv:2604.15303 rules out growth `≤ exp(n^{1/40})`. It was
     not read.
   - The tools would be contracting branch groups. Hard.
4. **20.110, 20.111 (M. Vannacci).** Are there residually finite hereditarily just-infinite
   groups that are:
   - amenable but not elementary amenable;
   - of intermediate growth;
   - self-similar but not linear?

   Hard.
5. **21.116 (E. Schesler).** Is every branch group boundedly acyclic? This needs
   bounded-cohomology tools that no lane has.

## Already owned or on main (do not reassign)

- **Our results:**
  - 21.73 and 21.74(b),(c): settled negatively.
  - 21.74(a): decidable on V.
  - 21.75: bh-free-37.
  - 20.44: reduced to totally consumable groups.
- **21.41:** node `torsion-free-fp-metabelian-self-similar-group-contains-z-wr-z`, OPEN.
  Kochloukova–Luiz conjecture NO. It is adjacent to bh-kd2p.
- **21.45 and 21.46:** bh-kourovka-2146 owns 21.46.
- **21.140:** crux `basilica-hnn-extension-is-fp-infinity`.
- **21.146:** node `zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`.
- **20.7:** the BH root.
- **21.143–21.145** (Thompson's F: automaticity, Brin–Sapir, quasi-isometry): well-known
  problems, not recommended.
