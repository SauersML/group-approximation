---
rg: 2
id: rattaggi-simple-lattices-are-not-left-orderable-proof
kind: route
title: A verified unsatisfiable sign-choice certificate on the radius-4 parity ball refutes every positive cone
target: rattaggi-simple-lattices-are-not-left-orderable
requires: []
artifacts:
  - experiments/lo-certificate-tree-lattices-2026-09-17/verify_certificate.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/certificate-incoherent-kernel-L4.txt
  - experiments/lo-certificate-tree-lattices-2026-09-17/certificate-sigma-kernel-L4.txt
  - experiments/lo-certificate-tree-lattices-2026-09-17/certificate-a6-kernel-L6.txt
  - experiments/lo-certificate-tree-lattices-2026-09-17/lo_search.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/bmw.py
  - experiments/lo-certificate-tree-lattices-2026-09-17/README.md
---

**Lemma (certificate soundness).** Let `H` be a group and `E ⊂ H \ {1}` a finite set closed
under inversion with no element of order 2. Let `T` be a set of triples `(p, q, r)` in `E^3` with
`p q = r` in `H`. If no `P : E → {0,1}` satisfies `P(g^-1) = 1 - P(g)` and `P(p) ∧ P(q) ⇒ P(r)`
for all triples in `T`, then `H` is not left-orderable.

*Proof.* A left order `<` on `H` has positive cone `C = {h : h > 1}`. It is a semigroup, since
`p, q > 1` gives `pq > p > 1`. For every `h ≠ 1`, exactly one of `h` and `h^-1` lies in `C`.
So `P(g) = [g ∈ C]` satisfies every constraint, a contradiction. □

**Step 1: the relators are Rattaggi's.** The square lists in `bmw.py` are transcribed from the
arXiv TeX sources of math/0507363 (the list `R_Γ` defining Λ) and math/0411546 (`R_Δ` plus the
12 further squares of `Σ`). The class `BMW` asserts that the link is complete bipartite: exactly
one square for every pair consisting of a b-letter `v^±1` and an a-letter `u^±1`, which gives
`4mn` swaps. This is the defining property of a `(2m,2n)`-group and a nontrivial consistency check
on the transcription. `test_bmw.py` checks:
- every relator evaluates to 1;
- the multiplication is associative on random triples;
- the embedded `F_2 × F_2` of math/0507363 commutes, as the paper states.

**Step 2: each triple is a product relation.** `verify_certificate.py` imports only the relator
strings. For each line `p ; q ; r` it rewrites the word `p q r^-1` to the empty word using only:
- free reductions;
- replacing a subword `v u` (v a b-letter, u an a-letter) by `u' v'`, but only after checking
  that `v u v'^-1 u'^-1` is a cyclic rotation of a relator or of its inverse.

Each step is an equality in `Γ`, so reaching the empty word proves `p q = r`. Soundness uses no
uniqueness of normal forms.

**Step 3: all elements are nontrivial, in `Γ_0`, and not involutions.**
- Every word has even a-length and even b-length, so it lies in `Γ_0`.
- Rewriting a word by Step 2's moves ends in a word `A B`, with `A` a reduced a-word and `B` a
  reduced b-word. Such a word is nontrivial when nonempty, because `Γ` acts on
  `T_2m × T_2n` simply transitively on vertices, and `A B` moves the base vertex to a vertex at
  combinatorial distance `(|A|, |B|)` (Bridson–Wise normal form). The verifier asserts nonempty
  normal words.
- Since `Γ` is torsion-free (a CAT(0) cube-complex group), no element equals its inverse.
- Distinct variables are assigned only to distinct normal words. Identifying two words that are
  proven equal can only add constraints to the CNF, and splitting one element into two variables
  can only remove constraints. So an UNSAT verdict on the verifier's CNF implies an UNSAT verdict
  for the true sets `E` and `T`. Soundness therefore needs only that the verifier never gives one
  variable to two unequal elements, and every identification is proven by rewriting.
- When a word's inverse is already named, the verifier sets the word's variable to the negation
  of the inverse's.

**Step 4: unsatisfiability.** The verifier runs a self-contained complete DPLL: indexed unit
propagation, then branching on each variable both ways. It returns "satisfiable: False" only
after exhausting the search tree.

**Outputs (2026-09-17, commands in README.md).**
- `verify_certificate.py incoherent certificate-incoherent-kernel-L4.txt kernel` gives
  `triples verified: 301 variables: 199 / DPLL nodes: 1015 / CNF satisfiable: False / CERTIFICATE VALID`.
- `verify_certificate.py sigma certificate-sigma-kernel-L4.txt kernel` gives
  `triples verified: 207 variables: 123 / DPLL nodes: 623 / CNF satisfiable: False / CERTIFICATE VALID`.
- `verify_certificate.py a6 certificate-a6-kernel-L6.txt kernel` gives
  `triples verified: 412 variables: 300 / DPLL nodes: 23439 / CNF satisfiable: False / CERTIFICATE VALID`.
- The certificates were found independently with CaDiCaL 1.5.3 (pysat) by `lo_search.py GROUP L
  kernel 2`, with L = 4, 4 and 6 and minimised by deletion. Every proper subset tested SAT during deletion, so each
  certificate is a minimal unsatisfiable set.

**Negative controls.**
- Deleting one triple makes the verifier print `certificate INVALID`.
- Corrupting a word triggers `triple not a product`.
- The same pipeline proves the Promislow group non-LO at radius 2, 3 and 4
  (`calib_promislow.py`, affine-matrix model).
- It finds the CNF satisfiable for the bi-orderable `F_2 × F_2` at radius 2, 3 and 4.

**Conclusion.** By the Lemma, `Λ = Γ_0`, `Σ_0` and the A6 kernel `Λ_0` are not left-orderable. Simplicity, torsion-
freeness and finite presentability are Rattaggi's theorems as cited in the claim; type F follows
from the finite locally CAT(0) square complex. □

*Review status.* The certificates are machine-checked twice, by two independent code paths
(normal-form multiplication with CaDiCaL, and relator rewriting with DPLL). No human has checked
them line by line. The relator lists were re-extracted mechanically from the arXiv TeX sources on
2026-09-17 (regex over the `R_Γ`, `R_Λ`, `R_Δ` and `R_Σ` arrays) and agree as sets with `bmw.py`
(30, 9, 12 and 12+12 squares); all three verifier runs were repeated with the same outputs. The
remaining trust points are the TeX sources themselves, and the identification of the kernel `Γ_0` with Rattaggi's `Λ` and `Σ_0`. Both papers
define it by this parity map.
