# ms-traces-3: the word-problem reduction WP(G_X) ≤_T L(X) in simple_kazhdan_sofic_group.tex

Lane `ms-traces-3`, reassigned by main (09-13 ~19:40). This file is written by ms-traces-3 only.

## Target
- The piece (c) of section "Word problems": "L(X) computes the word problem".
  - origin/main 2050a8eed (md5 65d47cb4504a421fbbd69a8a8620a71b): tex l.194–200.
  - bf961c128: l.240–241.
- Printed route: multiplying out a word gives a matrix with entries Σ_j f_j u^j, each f_j a table on words, using uf = (f∘T⁻¹)u. The word is trivial iff the tables of its difference from I₃ vanish on L(X).
- Owner of the section and of the Prop spellings: skf-degrees (statements module `SimpleKazhdanSofic/WordProblemDegreeStatements`). The (c) Prop spelling is being agreed in one message.

## CLAIM
- CLAIM `GroupApproximation/Computability/OracleTruthTable.lean`: truth-table reductions are Turing reductions. This is the oracle-relative primitive layer over Mathlib's `Nat.RecursiveIn`.
- CLAIM `GroupApproximation/Manuscript/SimpleKazhdanSofic/CylinderTables.lean`: finite sums of cylinder monomials `1_[v at o]·u^j` in LC(X,F₂)⋊ℤ, their arithmetic, and evaluation into `R S`.
- CLAIM `GroupApproximation/Manuscript/SimpleKazhdanSofic/WordNormalForm.lean`: 3×3 matrices over monomial sums, generator symbols, and the normal form of a word with its evaluation.
- CLAIM `GroupApproximation/Manuscript/SimpleKazhdanSofic/WordProblemReducesToLanguage.lean`: the vanishing criterion on L(X), primitive recursiveness, and the endpoint `printedWordProblemReducesToLanguage`.

## Status
- Module plan fixed; OracleTruthTable being written. The size estimate is reported to main if the development exceeds ~3500 lines.
