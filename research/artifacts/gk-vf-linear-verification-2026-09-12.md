# Linear-lift family: independent verification record

Lane `gk-vf-linear`, 2026-09-12. This lane is the verifier for the linear-lift family. Every item below
was re-derived from the statements and the Leavitt relations `t_i s_j = delta_ij`, `s0 t0 + s1 t1 = 1`.
None was checked by rereading the author's argument.

Conventions: `R = L_(F_3)(1,2)`, `G = R^x`, `S = F_3[G]`, `z = -1`, `eps_(+-) = 2(1 +- [z])`,
`w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e = 2(1 + [w])`, `e_- = eps_- e`. All arithmetic is mod 3.

## 1. Swap-separated reformulation of the anti-central corner: PASS

Items checked: artifact `ternary-swap-separated-pairs-2026-09-12.md`, Theorem 1 and Corollary 2;
the routes `swap-separated-pair-gives-anti-invariant-corner` and
`anti-invariant-corner-gives-swap-separated-pair`; the claim
`ternary-twisted-algebra-has-swap-separated-one-sided-pair`.

**Basic identities.**
- `eps_+^2 = 4(2 + 2[z]) = eps_+`, `eps_+ + eps_- = 4 = 1`, `eps_+ eps_- = 4(1 - [z]^2) = 0`, and
  `[z] eps_- = -eps_-`.
- `w^2 = s0 t1 s1 t0 + s1 t0 s0 t1 = s0 t0 + s1 t1 = 1`, and `d^2 = s0 t0 + s1 t1 = 1`.
- `d w = s0 t1 - s1 t0` and `w d = -s0 t1 + s1 t0 = -(d w)`. So `d w d = -w = z w`, and `w d = d z w`.
- `e^2 = 4(2 + 2[w]) = e`. Also `[d] e_- [d] = eps_- 2(1 + [z][w]) = eps_-(2 - 2[w]) = eps_-(2 + [w])`,
  and `eps_- - e_- = eps_-(1 - 2 - 2[w]) = eps_-(2 + [w])`. The two agree.
- Hence `e_- [d] e_- = e_- (eps_- - e_-) [d] = 0`, and `[w] e_- = e_-`.

**(P) => (C).** Take `c' = c(1 + [w])` and `b = a`. Then
`c' e_- b = 2 c (1 + [w])^2 a = 4 c (1 + [w]) a = c a + c [w] a = eps_-`.

**(C) => (P).** Take `b' = e_- b`, `c'' = c e_-`, `a = 2(b' + [d] b')` and `chat = c'' + c''[d]`.
- Both cross terms equal `c'' [d] b' = c e_- [d] e_- b = 0`. So `chat a = 2 . 2 c'' b' = eps_-`.
- `[w][d] b' = [d][z][w] b' = -[d] b'`, because `[z]` acts as `-1` on `S_-` and `[w] b' = b'`.
  So `[w] a = 2(b' - [d] b')`, and `chat [w] a = 2(c'' b' - c'' [d][d] b') = 0`.
- `a` and `chat` lie in `S_-`, because `[d]` commutes with the central `eps_-`.

**(P) <=> (E).**
- `p = a c` is idempotent and equivalent to `eps_-`, and `p [w] p = a (c [w] a) c = 0`.
- Conversely, take an equivalence `c a = eps_-`, `a c = p`. Then `c = c p` and `a = p a`, so
  `c [w] a = c p [w] p a = 0`.

**(X) => (P).** With `m = c[w]a`, `c[w][w]a = c a = eps_-`, and `u = (eps_- - m^2)^(-1)` in `S_-`,
put `c' = u(c - m c[w])`. Then `c' a = u(eps_- - m^2) = eps_-` and
`c' [w] a = u(m - m eps_-) = 0`. A nilpotent `m` makes `eps_- - m^2` a unit by the geometric
series, which is Corollary 2.

**Section 2 claims.**
- In `R`, `w s0 = s1`, so `t0 w s0 = t0 s1 = 0`, and `(s0, t0)` satisfies (P).
- Right translation `(a[g], [g^-1]c)` preserves (P) because `eps_-` is central. Left translation by
  `h` in `C_G(w)` preserves it too.
- Augmentation gives `eps(c) eps(a) = 1` and `eps(c) eps(a) = 0` in any algebra with a unital map
  to a field. So (P) is impossible in `F_3[PG]`.
- `S_- ~= M_2(T)` because `e_-` and `eps_- - e_-` are conjugate by `[d]`. A unital map
  `M_2(T) -> k` into a commutative ring sends the diagonal units to equal orthogonal idempotents
  summing to 1, which forces `1 = 0`. So `S_-` admits no such map.

**Scope: finite-dimensional representations.**
- `G` has no nontrivial finite-dimensional representations: its image would be finitely generated
  linear, hence residually finite.
- `G` has no nontrivial finite quotient. A finite-index normal `N` maps onto `PG` or into `{±1}`.
  Simplicity of `PG` and perfectness of `G` then force `G/N = 1`.
- So every such representation of `S` factors through augmentation on `S_+` and kills `S_-`, as the
  artifact says.

Verdict: exact. Theorem 1 is an equivalence of statements, and the claim stays OPEN.

## 2. Direct-product splitting (correction e2dcdae9b): PASS, second independent derivation

Item checked: route `anti-invariant-swap-corner-refutes-ternary-surjunctivity`.

From `c e_- b = eps_-` with `b, c` in `S_-`, put `A = e_- b + eps_+` and `C = c + eps_+`.
- Since `c eps_+ = 0`, `eps_+ e_- = 0` and `eps_+^2 = eps_+`, we get `CA = eps_- + eps_+ = 1`.
- `AC = e_- b c + eps_+`. If `AC = 1`, then `e_- (bc) = eps_-`, so `e_- = e_- e_- (bc) = eps_-`.
- But `eps_- - e_- = eps_-(1 + 2[w]) = 2(1 + 2[w] - [z] - 2[zw])`. Its coefficients are nonzero on
  the four distinct elements `1, w, z, zw`. These are distinct because `w s0 = s1` is neither `s0`
  nor `-s0`.
- So `F_3[G]` is not directly finite, and `stable-finiteness-failure-refutes-surjunctivity` gives an
  injective, non-surjective linear automaton on the full shift `F_3^G`.

Statement fidelity: this is the full shift over `G`, not a subshift. The automaton is the identity
on the invariant summand and strict on the anti-invariant one, and both summands are linear direct
summands of `F_3^G`.

The companion routes `projective-swap-corner-refutes-ternary-surjunctivity` and
`ternary-swap-fullness-projects-to-anti-invariant-half` also pass:
- in `F_3[PG]`, `ebar = eps_+` forces `wbar = 1`, which is false;
- multiplying by the central idempotent `eps_-` projects the unit-group equation onto `S_-`.

**One-decidable-host rule.** A solution is a finite identity in `F_3[G]`, and `G` has a decidable
word problem. So a certificate is checkable in one host, and no surjunctive quotient is used.

## 3. F_3-linear soficity gate (cd4162f9b): PASS

Items checked: routes `f3-linear-soficity-refutes-projective-swap-fullness` and
`non-linear-sofic-via-projective-ternary-swap-fullness`, and the claims
`projective-ternary-group-is-f3-linear-sofic` and `projective-ternary-swap-idempotent-is-not-full`.

- `c ebar b = 1` gives `y x = 1` with `x = ebar b` and `y = c`.
  - If `x y = 1`, then `ebar` is right invertible, so `ebar = 1` and `wbar = 1`, which is false.
  - So `F_3[PG]` is not directly finite.
  - Linear sofic groups over `F_3` have stably finite group algebras
    (`linear-sofic-group-algebra-is-stably-finite`), which contradicts the gate.
- A non-directly-finite pair in `F_3[PG]` stays one in `F[PG]` for every field `F` containing
  `F_3`. It also lives in `F_3[H]`, where `H` is generated by the supports of `b`, `c` and
  `wbar`. So the contrapositive route and its localization remark are sound.
- The payoff paragraph is sound:
  - linear soficity passes to subgroups, and `G` embeds in `PG`;
  - a stably finite `S = S_+ x S_-` has no one-sided pair in either factor, because padding by the
    other factor's unit gives a pair in `S`.
- The claim correctly declines to assert that linear soficity descends to `PG` from `G`.

## 4. Scope of the s0-lift search records (b1418d097, 4cd7be203): PASS as scoped

Item checked: node `left-invertible-lift-of-s0-in-leavitt-group-algebra`.
- **Span bound.** A lift `a` with `pi(a) = s0` and `supp a` in `B_r` puts `s0` in
  `span pi(B_r)`. So "`s0` is not in `span pi(B_2)`" gives radius at least 3 over the atlas-chart
  generators, exactly as stated. The Gaussian elimination itself was not recomputed here, since
  this lane runs no heavy compute.
- **Two-sided mode.** The node correctly says that imposing `pi(b) = t0` restricts the search
  rather than deciding the one-sided instances.
- **UNSAT verdicts.** The node correctly records them as solver outputs without proof logs,
  excluding only the searched support pairs.
- No overstatement found.
