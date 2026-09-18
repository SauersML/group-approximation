# Referee report (gq-referee-a, proof-gap lens): KMS configuration letters inherit exponent p

**Reviewed:** `kms-configuration-letters-inherit-exponent-p` and its route `-proof` (lane gq-infinite-primes,
178d7a40e), read on origin/main.

**Verdict: PASS.** No gaps found. The relation statements, `A_i ∈ M_i`, and the shape of `U` are taken from the KMS
source; checking them is the citation lens.

## Checks
Conventions: `u^a = a^{-1}ua` and `[x,y] = x^{-1}y^{-1}xy`.
- **G5 a).** `[x_u, A_i] = x_{uA_i}` gives `A_i^{-1} x_u A_i = x_u x_{uA_i}`, that is, `x_u^{A_i} = x_u x_{uA_i}`.
- **G5 c).** With `u' = uA_i` and `z = A_i ∈ M_i`, it gives `x_{uA_i}^{A_i} = x_{uA_i}`.
- **The induction.** `x^{A^{n+1}} = (x^{A^n})^A`, and conjugation is a homomorphism, so
  `(x_u x_{uA_i}^n)^{A_i} = x_u x_{uA_i} · x_{uA_i}^n = x_u x_{uA_i}^{n+1}`.
  - This is just associativity. **G7 is not needed at this step**, although it is harmless.
- **Conclusion.** `A_i^p = 1` (G1) gives `x_u = x_u x_{uA_i}^p`, so `x_{uA_i}^p = 1`.
- **Coverage.** Every `v ∈ U` that contains some `A_i` equals `uA_i`, with `u` the word `v` with that `A_i` removed.
  So every such `x_v` has order dividing `p`.

## Scope
- **The G8 conclusion is correctly conditional.** It rests on KMS Lemma 4.5 (`T` abelian). Given that, a product of
  conjugates of elements of order dividing `p` has order dividing `p`.
- **The "Reading" paragraph is heuristic.** It says a torsion-free base forces the letters `x_{uA_i}` to be trivial,
  unless the `A`-letters are made torsion-free. This is an accurate reading, but a design remark, not a theorem.
