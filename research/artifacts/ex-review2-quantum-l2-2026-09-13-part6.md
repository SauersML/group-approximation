# EX review, second wave, quantum and L²: part 6. The KMS group with stop relations, an independent check of logic-quantum's repair

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Why this item.** ex-verify-logic-quantum wrote `kms-group-with-stop-relations-simulates-all-words` as the
repair of its own GAP (logic-quantum part 1 §1.4). It asked for an independent verifier. The zero-element
clause of KMS Theorem 4.3(b) feeds the Pi^0_2-completeness of RF_fp and LEF_fp.

**Source.** Kharlampovich–Myasnikov–Sapir arXiv:1204.6506v5, extracted with ghostscript on MSI
(`/scratch.global/sauer354/ex/ex-verify2-quantum-l2/pdf/1204.6506v5.txt`). Line numbers refer to that file.

## 6.0 Verdict

| claim | verdict |
|---|---|
| `kms-group-with-stop-relations-simulates-all-words` (+ `-proof`) | PASS at the checked steps. The KMS Lemmas 3.1 (group form), 4.9–4.12 and 4.14 were read at source, and their proofs taken as printed |

## 6.1 The source facts used

- **S(M)** (l. 15–41). Its relations are:
  - (2), commutativity;
  - (3), the stop relation `q_0 = 0`;
  - the 0-relations `xy = 0` for two-letter words that are not subwords of a configuration word
    `q_i a_1^(ε_1)...a_K^(ε_K) A_1...A_K` modulo (2);
  - (4), the Minsky relations: `q_i = q_j a_(n_1)...a_(n_m)` (Add), `q_i a_(n_1)...a_(n_m) = q_j` (Sub),
    and `q_i A_(n_1)...A_(n_m) = q_j A_(n_1)...A_(n_m)` (zero test).
- **G(M)** (l. 932–1030).
  - Generators `L_0 = {x_u : u = q_j w, w in U_0}`, where `U_0` is the set of divisors of `A_0 A_1...A_K`,
    plus `L_1` and `L_2`.
  - Relations G1–G8. G8 gives one relation per command, including commands into `q_0`, in the `*`
    notation.
  - None of G1–G8 sets `x_(q_0 w) = 1`.
- **Theorem 4.3(b)** (l. ~1040–1050) is the equivalence of the words (12) in `G(M)` and in `S(M)`.
- **The model group `Ḡ`** (l. 1184–1300).
  - `Š` is `S(M)` without the relations (4), with the stop relation kept. `W` is the set of nonzero
    elements of `Š` with a `q`-letter, and `W_0` consists of these read in `S(M)`, with `A_0` inserted.
  - `T_1` is the elementary abelian `p`-group on the `z_(i,u)`, and the automorphisms are given by (13).
- **Lemma 4.9** (l. 1360–1365): `z_(1,u) * w = z_(1,uw)`, "where we set z_(1,0) = 1 (the identity element)".
- **Lemmas 4.10–4.11.** `φ(x_u) = z_(1,u)` is an onto homomorphism, with preimages `x_(i,w)` defined by
  conjugation (`x_(i+e_j,w) = x_(i,w)^(-(a_j')^-1)`, `x_(i+2e_j,w) = x_(i,w)^(a_j^-1)`,
  `x_(i,w) * a_j = x_(i,w a_j)`, `x_(i,w) * A_j = x_(i,w A_j)`).
- **Lemmas 4.12 and 4.14** (l. 1455–1500): the `x_(i,w)` span `T`, and their images are independent in
  `T_1`.

## 6.2 Re-derivation

- **Clause 1.**
  - `G_0` is a quotient of `G(M)`, so it lies in `A_p^2 A ∩ ZN_(K+1) A` (Thm 4.3(a); varieties are closed
    under quotients).
  - In `S(M)`, `q_0 w = 0`, so `φ(x_(q_0 w)) = z_(1,0) = 1` by Lemma 4.9's convention. So `φ` factors through
    `G_0`, still onto.
- **Clause 2, "if", nonzero elements.**
  - Equal nonzero elements of `S(M)` are joined by a chain of commutativity and Minsky steps between
    configuration-type words, none of them `0`.
  - KMS Lemma 3.1 for `G(M)` turns each step into a group equality, using G1, G2, G8 and the permutation
    equalities (12). Those relations survive in `G_0`.
- **Clause 2, "if", zero elements.**
  - Let `V = q_i a^m A^α` be `0` in `S(M)`. A semigroup word with zero equals `0` iff a chain of
    elementary steps reaches a word containing a zero relator: `q_0`, or a two-letter 0-word.
  - From a configuration-type word, the Minsky relations insert or delete letters next to the `q`-letter,
    and they never place `a_n` after `A_n`. Commutativity permutes letters. So no 0-word appears, and the
    chain first meets `0` when a Minsky step creates `q_0` (a command into `0`), or `i = 0` from the start.
  - Every step before that one, and that step itself (G8 has relations for commands into `0`), is a group
    equality. So the word of `V` equals `x_(q_0 A_0) * (letters)`.
  - In `G_0`, `x_(q_0 A_0) = 1`. Then `1 * a_i` is a product of conjugates of `1` and `1 * A_i = [1, A_i]`, so
    both are `1`. So every word of a zero element is `1`.
- **Clause 2, "only if".**
  - Equality in `G_0` gives equality in `Ḡ`.
  - There a word of a nonzero `u` is the basis vector `z_(1,u)`: Lemma 4.9 with `u = q_i A_0 a^m A^α`,
    read in `W_0` modulo `S(M)`. A word of `0` is `1`.
  - Distinct nonzero elements give distinct basis vectors, and no basis vector is `1`.
- **Clause 3.**
  - By clause 2, `x_(1,w) = 1` when `w = 0` in `S(M)`. The conjugation formulas carry `1` to `1`, so by
    induction on `sum i_j`, `x_(i,w) = 1`.
  - Lemma 4.12's spanning argument produces `z_(i',0)` exactly where the group element is such an
    `x_(i',w')` with `w' = 0`, and that element is now `1`. So the `x_(i,w)` with `w` nonzero span `T_0`.
  - Lemma 4.14's independence half maps them to a basis of `T_1`. A spanning set mapped bijectively onto a
    basis gives an isomorphism `T_0 -> T_1`.

## 6.3 Scope and not re-checked

- The claim's evidence that the repair is *needed*: the automorphism model over `S(M)` without the stop
  relation, which satisfies G1–G8 and separates stop configurations. That is logic-quantum's GAP finding,
  and it is not re-derived here. The repair is correct whether or not `G(M)` already identifies these
  words.
- The remark on the published version (Bull. Math. Sci. 7 (2017), §3.1 p. 325 and Remark 3.10 p. 328) was
  not re-read.
- The printed proofs of Lemmas 3.1 (group form), 4.12 and 4.14 were not re-derived line by line.
