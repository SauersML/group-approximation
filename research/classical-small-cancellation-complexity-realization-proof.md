---
rg: 2
id: classical-small-cancellation-complexity-realization-proof
kind: route
title: Prove the C'(1/6) family is uniform by unique block exponents, detect r_n by Greendlinger, and hide a hard decidable set in the relator index
target: small-cancellation-groups-realize-every-wp-complexity
requires: [complexity-bounded-host-classes-are-not-universal]
---

Inputs: Greendlinger's lemma and Dehn's algorithm for arbitrary, possibly infinite,
symmetrized `C'(1/6)` sets of relators (Lyndon--Schupp, *Combinatorial Group Theory*,
Ch. V, Thms 4.4 and 4.5; textbook, not re-read at source). Also the deterministic
time hierarchy for recursive bounds.

**1. `C'(1/6)`.**
- Each block `a b^e` of the family has an exponent `e`. Exponents of `r_n` lie in
  `[c_n+1, c_n+13]`, and `c_(n+1) = 4c_n >= c_n + 14`. So every exponent occurs in
  exactly one block of exactly one relator.
- A common subword of `r` and `s^(-1)`, for `r, s` in the family, is empty, since
  `r` has only the letters `a, b` and `s^(-1)` only `a^(-1), b^(-1)`. So pieces
  come from two occurrences in positive cyclic words.
- If a piece `u` contained a full segment `a b^e a`, the unique exponent `e` would pin
  both occurrences to the same place of the same cyclic word. That is not a piece.
- So a piece is `b^s a b^t` or `b^s`, with `s, t` bounded by two exponents of the
  shorter relator `r_n` involved. So `|u| <= 2(c_n + 13) + 1 = 2c_n + 27`.
- Now `|r_n| = 13c_n + 104`, and `2c_n + 27 < (13c_n + 104)/6` exactly when
  `c_n > 58`, which holds since `c_n >= 200`. The other relator is longer, so the
  bound holds for it too.
- Each `r_n` is cyclically reduced and not a proper power. So `G_A` is torsion-free
  (Lyndon--Schupp V.10, torsion in `C'(1/6)` groups comes only from proper-power
  relators).

**2. Detection.**
- If `n in A`, then `r_n = 1` by definition.
- Let `n` not be in `A` and suppose `r_n = 1` in `G_A`. The word `r_n` is nonempty
  and cyclically reduced. By Greendlinger's lemma, some cyclic permutation of `r_n`
  contains a subword `u` of a cyclic permutation of some `r_m^(±1)`, `m in A`, with
  `|u| > |r_m|/2`.
- Since `m ≠ n`, `u` is a piece of the full family, which is `C'(1/6)` by step 1.
- So `|u| < |r_m|/6`. Contradiction.

**3. Decidability.** A relator can have more than half of itself inside `w` only if its
length is at most `2|w|`. The set of `n` with `13c_n + 104 <= 2|w|` is finite and
computable, and membership of each such `n` in `A` is decidable. So Dehn's algorithm
runs with a finite, computable relator list.

**4. Complexity.**
- Given recursive `T`, let `T^(m) = max_(k<=m) T(k)` be its recursive monotone majorant.
- Put `g(n) = n*T^(4^(n^2)) + 4^(n^2)`. The standard diagonalization gives a decidable `A` that no algorithm decides in time `O(g(n))`, even after finitely many exceptions.
- Suppose the word problem of `G_A` had an algorithm in time `C*T(C*l) + C*l + C`.
  - Run it on `r_n`, which has length `13c_n + 104 <= C_0*4^n` and can be written in time `O(4^n)`.
  - This decides `n in A` in time `C*T^(C*C_0*4^n) + O(4^n)`, which is `<= g(n)` for all large `n`.
  - That contradicts the choice of `A`.

**5. Consequence.**
- Let `H = <Y>` be finitely generated with solvable word problem, with decider time
  `t_H` (a recursive function).
- If `G_A <= H`, write `a, b` as fixed words in `Y`. Substitution turns a length-`l`
  word into a length-`<= K*l` word, so `G_A` has word problem in time
  `t_H(K*l) + K*l`.
- Choose `A` by item 4 for `T = t_H`. Then `G_A` embeds in no such `H`.
- The class statement is the same argument with the uniform bound. `∎`
