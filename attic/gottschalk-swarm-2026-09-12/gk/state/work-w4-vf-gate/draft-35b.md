
### 35.4 Lemma 6.1 (Section 6). CORRECTION to the hypothesis; PASS in the corrected form

**The literal statement is false.** Read literally, the hypothesis says that each positive root of the frames at `A`
and `A1` moves all its points strictly one way. Under that hypothesis the conclusion "all of them move the same way"
fails, and `b` preserves some such order.

- **Counterexample.** Identify `[A]` with `X` through `Ay -> y`. On `[A]`, `b` is `0y -> 0y`, `10y -> 100y`,
  `110y -> 11y`, `111y -> 101y`. Let `phi_2(0y) = 1 phi_2(y)` and `phi_2(1y) = 0y`, and put
  `Psi = (0y -> 0y, 10y -> 10y, 111y -> 110y, 110y -> 111 phi_2(y))`. Order `[A]` by `xi ≺ eta` iff
  `Psi(xi) <_lex Psi(eta)`, and order the rest of `X` lexicographically, with the block `[A]` in its place.
- **`b` preserves `≺`.** Recomputed: `Psi b Psi^(−1)` is `0 -> 0`, `10 -> 100`, `110 -> 101`, `1110 -> 110` and
  `1111 -> 111`. For the last two:
  - `phi_2^(−1)(0w) = 1w`, and `1110w -> 110 1w -> 111w -> 110w`;
  - `phi_2^(−1)(1w) = 0 phi_2^(−1)(w)`, and `1111w -> 110 0 phi_2^(−1)(w) -> 11 0 phi_2^(−1)(w) -> 111w`.

  The domain code `0 < 10 < 110 < 1110 < 1111` goes to `0 < 100 < 101 < 110 < 111`, so this is in `F`, and `b`
  preserves `≺`.
- **Directions.** The blocks are ordered `[A0] ≺ [A10] ≺ [A111] ≺ [A110]`. So:
  - at `A`, `S[A0]T[A10]`, `S[A10]T[A11]` and `S[A0]T[A11]` move down;
  - at `A1`, `S[A10]T[A110]` and `S[A10]T[A111]` move down, but `S[A110]T[A111]` moves up.

  Every root moves its points strictly one way, not all the same way, and `b` preserves the order.
- **Where the proof slips.** "Same direction" shows only that `S[A10]T[A110]` follows the roots at `A`. The root
  `S[A110]T[A111]` compares two subcylinders of `[A11]`, and no root at `A` constrains them.

**Corrected statement.** Consider total orders on `X` in which the positive roots of each frame all move points
strictly one common way. Then both frames move the same way, and no such order is preserved by `b`.
- The artifact's two steps prove this.
- "Same direction" transfers the direction of the frame at `A` to `S[A10]T[A110]`, and so to the whole frame at `A1`.
- "Not preserved" uses the downward roots `S[A10]T[A110]` and `S[A110]T[A111]`. They give `[A100] ≺ [A11] ≺ [A101]`,
  which is impossible because `[A101] ⊆ [A10] ≺ [A11]`.

**Consequences.**
- **Section 6, item 1.** "Lemma 6.1 rules out the mechanism of Theorem 3.5" stands. That mechanism needs all six roots
  in one `T_≺`, which is one common direction.
- **Contraction.** `b` sends `[A10 0^k]` onto `[A10 0^(k+1)]`. On `[A1]` it is three prefix replacements, so Section 2
  does not apply.
- **What the counterexample does not show.** It gives no amenability or soficity of `Gamma_b`, which stays open.
- **Wording to correct forward.** Two sentences use the literal wording, "no order preserved by `b` makes both frames'
  positive roots monotone":
  - the Scope of `lex-decreasing-units-with-order-preserving-letters-are-amenable` (line 38);
  - the w7-sub-multiletter entry on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (line 231).

  Both should say "monotone in one common direction". The plans artifact (line 426) already says "all move one way",
  which is correct. No claim statement depends on the literal version.

### 35.5 Model tests, displays, routes, subsumption and scope. PASS

- **Section 5, item by item.**
  - Free sofic model: Proposition 2.3 with Theorem S's `rho` gives `(3/8)^2` on the sofic `G wr S_2`.
  - Finite subgroups: the order-128 group lies in `UT_3(R) <= U_<`, as in 35.2.
  - Right-child items 2–4:
    - the four positive roots lie in `T_<`, since `A0 < A10 < A110 < A111`;
    - `x^A_12(s_0) x^A_21(1)` uses a negative root;
    - the frame entries of `iota_A(w_23)` include `s_0`, `s_1`, `t_0`, `t_1`, and `b` contracts `e_(A10)`.
  - Jacobson nodes: `binary-jacobson-el3-is-sofic` and the halves node read as in Sections 31–32 here, and property (T)
    with residual finiteness is no conflict.
  - Depth-monotone: Example 3.6(2) and Corollary 4.4.
  - Ternary target: line 29 records `theta = 1` for independent factors.
  - Toeplitz quarter: its group lies in `U_<`.
- **Claim displays.**
  - Split-cylinder: Statements 1–3 are Lemmas 2.1–2.2 and Proposition 2.3 as re-derived in 35.1. The Consequence is
    Corollary 2.4. The Scope is Section 2's, including characteristic three.
  - Lex claim: items 1–4 are Lemmas 3.1–3.4, Theorem 3.5 and Example 3.6(1). The Consequences are 3.6(2), 3.7 and
    characteristic three. The Scope sentence is corrected in 35.4.
- **Entries.**
  - The entry on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (blob `da18a78a`) and the one on the
    ternary target summarize Sections 2–4 and the characteristic-three port accurately. The wording on line 231 is as
    in 35.4.
  - The plans record (blob `19de3bf9`, lines 412–426) is accurate.
- **Routes.**
  - `lex-decreasing-units-order-preserving-letters-amenability-proof` requires
    `sofic-subgroups-carry-independent-cylinder-defects`, which is ESTABLISHED. Its five steps are 35.2.
  - `split-cylinder-data-defect-firewall-proof` requires nothing, and Statements 1–3 are self-contained.
  - Advisory: the claim's Consequence uses Theorem S and the defect gap, both ESTABLISHED, and the route may list them.
- **Subsumption scan at `0bb651f36d`.** `tau_AB`, `wr S_k`, `U_<`, "lexicographically decreasing" and "Borel group" hit
  28 research files. Outside this lane's files the hits are other notation:
  - the sign involutions `[tau_(A_i)]` of the characteristic-three descent;
  - barycenters;
  - Steinberg coordinates;
  - `H wr S_k` for finite-index overgroups;
  - function-field Borel groups.

  The four-transvection escape artifact consumes `U_< ⋊ P` as a firewall. The right-child node (item 4) and Section 4
  of the locally-finite-conjugation artifact prove finiteness for four positive roots through a potential, and
  Lemma 3.2 generalizes that, which `distinct_from` records. No duplicate.
- **Scope.** Each firewall is conditional: a deficit from these relations would imply the gate, or would imply that
  `F` is nonamenable, or it contradicts Theorem S. None of them forces a rank model or `theta` to be trivial. The next
  live systems, `Gamma_b`, `U_< ⋊ F` and `EL_3(J)`, stay OPEN.
