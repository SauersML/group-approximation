# The logical form of Boone–Higman (lane bh-logic, 09-18)

These are lane proofs and have not been reviewed. No priority is claimed: part 1 of
the characterization is the classical Boone–Rogers-style semi-decision. This
artifact supports `common-decidable-hosts-iff-uniform-word-problem`,
`boone-higman-uniform-in-word-problem-algorithms` and their proof route.

## 1. Where the literature stops, and what was already on main

- Boone–Rogers (1966): the word problem is not uniformly solvable on the class of all
  finitely presented groups with solvable word problem. It follows that no
  "universal solvable word problem group" exists.
- `fp-simple-envelopes-not-computable-from-presentations` (on main): no algorithm
  computes an envelope from presentations with Dehn function `≼ n^18`, or from
  polynomial-time acceptors.
- `polynomial-dehn-fp-groups-have-nonuniform-word-problem` (on main): the underlying
  halting-indexed family.

## 2. New: the uniformity characterization

Everything is conditional on Boone–Higman where stated. For a c.e. class `𝒞` of
finite presentations the following are equivalent:
- uniformly solvable word problem;
- one finitely presented simple host, with computable embeddings;
- computable envelopes, possibly with varying hosts.

Unconditionally, uniformly solvable word problem is equivalent to having one
finitely presented host with solvable word problem.

Consequences:
- **Non-uniformity is exactly the obstruction.** A proof of Boone–Higman is
  automatically uniform on every c.e. class with uniformly solvable word problem, and
  non-uniform only where the word problem itself is not uniform.
- **Universal hosts cost nothing extra.** "One finitely presented simple group
  containing every hyperbolic group", or every one-relator group, follows from
  Boone–Higman.
  - Unconditionally it is OPEN, and it is a natural strengthening of
    Belk–Bleak–Matucci–Zaremsky's hyperbolic theorem. This is flagged for bh-cool.
  - Unconditionally there IS one finitely presented group with solvable word problem
    containing all hyperbolic groups, via HNN plus Clapham.
- **Hosts can't be bounded by complexity.** No finitely presented simple group
  contains all finitely presented groups with Dehn function `≼ n^18`.

## 3. Arithmetic complexity

Notation:
- `P` is a finite presentation and `e` an index. `A(P,e)` says "`φ_e` is total and
  decides the word problem of `G_P`".
- `(Q, φ)` is a finite presentation together with words for the generators of `P`.
  `C(P;Q,φ)` says "`Q` is simple, nontrivial, and `φ` is an injective homomorphism".

The complexity of each condition:
- `w =_P 1` is `Σ_1`.
- `A(P,e)` is `Π_2`. Totality is `Π_2`. The clause "output 0 ⇒ `w = 1`" is
  `∀w(Π_1 ∨ Σ_1)`, which is `Π_2`. The clause "output 1 ⇒ `w ≠ 1`" is
  `∀w(Π_1 ∨ Π_1)`, which is `Π_1`.
- `C` is `Π_2`:
  - homomorphism: finitely many `Σ_1` conditions;
  - nontriviality: a finite disjunction of `Π_1` conditions;
  - simplicity: `∀u (u =_Q 1 ∨ Q/⟨⟨u⟩⟩ = 1)`, which is `∀(Σ_1 ∨ Σ_1)`;
  - injectivity, given simplicity and nontriviality: `∀w (w =_P 1 ∨ Q/⟨⟨φ(w)⟩⟩ = 1)`,
    which is again `∀(Σ_1 ∨ Σ_1)`.
- Boone–Higman, in its finitely presented form (equivalent by Clapham), is
  `∀P∀e [¬A ∨ ∃(Q,φ) C]`, that is `∀(Σ_2 ∨ Σ_3)`, which is `Π_4`.
- UBH is `∃F ∀P∀e [¬A ∨ (F(P,e)↓ ∧ C(P;F(P,e)))]`. The matrix is `Σ_2 ∨ (Σ_1 ∧ Π_2)`,
  which lies in `Δ_3`. So UBH is `Σ_4`.

Both are arithmetic sentences, so forcing cannot change their truth value.

## 4. Open questions (logic side)

1. Does Boone–Higman imply UBH? By item 3 of the UBH node, a counterexample needs a
   non-c.e. spread of inputs.
2. Is Boone–Higman equivalent to a `Π_3`, or even `Π_2`, sentence? For example, via a
   canonical envelope construction whose simplicity is automatic, such as the shell
   envelopes, which are simple for every enumeration. Then only finite presentation,
   a `Σ_3` condition, would remain existential.
3. **Universal hosts.** Is there, unconditionally, a finitely presented simple group
   containing every hyperbolic group? Or every one-relator group?
