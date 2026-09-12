# Separated triangular steps flatten: Jordan certificates are visible to K_0

Lane `w5-upg-flatten`, 2026-09-12. Targets: `anti-central-triangular-certificates-flatten-to-minors` and step
(U1b), `anti-central-weakly-finite-images-carry-rank-functions`, of the audited ternary counterexample chain.

Notation as in `research/artifacts/state-upgrade-kill-test-2026-09-12.md`: `A` is a unital ring, `<~` is the
minor order (`M <~ N` iff `M = X N Y`), `(+)` is block sum, and a triangular step replaces `A (+) B (+) Z` by
`[[A, C], [0, B]] (+) Z`. Idempotent means an idempotent square matrix over `A`.

## 0. Summary

- **Lemma S (established).** A triangular step can be removed from a certificate whenever the carried
  idempotent minor *separates*: one part sees only `A` and part of `Z`, the other sees only `B` and a
  disjoint part of `Z`. This extends Proposition 3.1 of the kill-test artifact, where the carried minor had
  to split along `A`, `B` and `Z` separately. Mixing a diagonal block with free padding does no harm.
- **Corollary J (established).** If `u` is an `n x n` matrix with `u^k = 0` and `f` is an idempotent with
  `f <~ u`, then `f^((+)k) <~ I_((k-1)n)`. In `K_0`, `k[f] <= (k-1) n [A]`.
- **The (U1b) kill test is resolved.** A ring holding `u in M_4(W)` with `u^3 = 0` and
  `L u R = diag(1,1,1,0)` fails the rank condition, because `I_9 <~ f^((+)3) <~ I_8`. Weak finiteness is
  not used. So the "rank-level retract trick" asked for in the (U1b) node exists.
- **Consequence for (U1b).** Nilpotent Jordan data never obstructs one element at a time: the outer
  s-rank already obeys the Jordan bound `rho^s(u) <= (k-1)n/k`. A certificate that cannot be flattened
  must pass through a triangular step whose two diagonal blocks are mixed with each other, or with a
  common padding block.
- **Halving.** The unital map `M_2(S_-) -> S_-` transports certificates and shrinks sizes, but it is a
  ring map and preserves the mixing pattern, so it does not by itself unmix a step. It is not needed for
  Jordan certificates.
- Sections 3–5 (outer s-rank criterion, extension criterion, where it stops) follow in the next landing.

## 1. Lemma S: separated triangular steps

**Lemma S.** Let `A`, `B`, `C`, `Z_1`, `Z_2` be rectangular matrices over `A`, with `C` of the right size
for `T = [[A, C], [0, B]]`. Let `f`, `g` be idempotents with

    f <~ A (+) Z_1      and      g <~ B (+) Z_2.

Then `f (+) g <~ T (+) Z_1 (+) Z_2`.

By transposing block order the same holds with the roles of the two diagonal blocks exchanged, and after
permuting rows and columns the padding blocks may sit anywhere. `Z_1` or `Z_2` may be empty. With both
empty and `f`, `g` identities, Lemma S is Proposition 3.1 of the kill-test artifact.

*Proof.*
1. Write the two minors in block form:
   `f = L_A A R_A + L_1 Z_1 R_1` and `g = L_B B R_B + L_2 Z_2 R_2`, from
   `f = (L_A  L_1)(A (+) Z_1)(R_A ; R_1)` and `g = (L_B  L_2)(B (+) Z_2)(R_B ; R_2)`.
2. Order the rows of `W = T (+) Z_1 (+) Z_2` as (rows of `A`, rows of `B`, rows of `Z_1`, rows of `Z_2`), and
   its columns likewise. Then

       W = [[A, C, 0, 0], [0, B, 0, 0], [0, 0, Z_1, 0], [0, 0, 0, Z_2]].

3. Put `𝓛 = [[L_A, 0, L_1, 0], [0, L_B, 0, L_2]]` and `𝓡 = [[R_A, 0], [0, R_B], [R_1, 0], [0, R_2]]`. Then

       W 𝓡 = [[A R_A, C R_B], [0, B R_B], [Z_1 R_1, 0], [0, Z_2 R_2]],
       𝓛 W 𝓡 = [[L_A A R_A + L_1 Z_1 R_1, L_A C R_B], [0, L_B B R_B + L_2 Z_2 R_2]] = [[f, D], [0, g]],

   with `D = L_A C R_B`. The lower-left block vanishes because the rows of `B` and `Z_2` are zero under the
   columns of `A` and `Z_1`.
4. Compress: `diag(f, g) [[f, D], [0, g]] diag(f, g) = [[f, fDg], [0, g]]`.
5. Clear the corner: `[[f, fDg], [0, g]] · [[f, -fDg], [0, g]] = [[f, -fDg + fDg], [0, g]] = f (+) g`.
6. So `f (+) g = diag(f,g) 𝓛 W 𝓡 diag(f,g) [[f, -fDg], [0, g]]`, a minor of `W`. ∎

**What Lemma S does not cover.** It needs a decomposition `f (+) g` of the carried idempotent in which `f`
avoids the rows and columns of `B` and `g` avoids those of `A`, and in which `f` and `g` use disjoint
padding. The remaining triangular steps are those whose carried minor mixes `A` with `B`, or mixes both
with one common padding block. That is where a ring with the rank condition and no Sylvester rank function
has to live.

## 2. Corollary J: nilpotent Jordan certificates

**Corollary J.** Let `u` be an `n x n` matrix over `A` with `u^k = 0` for some `k >= 1`, and `f` an
idempotent with `f <~ u`. Then for every `1 <= j <= k`,

    f^((+)j) <~ I_((j-1)n) (+) u^j,

and in particular `f^((+)k) <~ I_((k-1)n)`. So `k [f] <= (k-1) n [A]` in `K_0(A)`, and every state `s` on
`(K_0(A), [A])` has `s(f) <= (k-1) n / k`.

*Proof.* Induction on `j`; the case `j = 1` is the hypothesis.
1. **Frobenius matrix.** For `n x n` matrices `V`, `U`, put `T = [[V, I_n], [0, U]]`. Then

       [[I, 0], [-U, I]] · T = [[V, I], [-UV, 0]],
       [[V, I], [-UV, 0]] · [[I, 0], [-V, I]] = [[0, I], [-UV, 0]],

   and permuting columns gives `I_n (+) (-UV)`. All factors are invertible, so `T <~ I_n (+) UV`.
2. **Step.** Take `V = u^j` and `U = u`. The induction hypothesis says `f^((+)j) <~ u^j (+) I_((j-1)n)`, and
   `f <~ u`. Lemma S with `A = u^j`, `Z_1 = I_((j-1)n)`, `B = u`, `Z_2` empty and `C = I_n` gives

       f^((+)j) (+) f <~ T (+) I_((j-1)n) <~ I_n (+) u^(j+1) (+) I_((j-1)n),

   which after permuting blocks is `f^((+)(j+1)) <~ I_(jn) (+) u^(j+1)`.
3. **End.** At `j = k`, `u^k = 0`, and `I_((k-1)n) (+) 0_(n x n) <~ I_((k-1)n)`.
4. **K_0.** `f^((+)k) <~ I_((k-1)n)` makes the projective module of `f^((+)k)` a retract of
   `A^((k-1)n)`, as in item 1 of Proposition B of the (U1a) artifact. ∎

**The (U1b) kill test.** Section 4 of `research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md`
asks for a nonzero weakly finite `W ⊇ M_4(K)` with faithful states, carrying `u in M_4(W)` with `u^3 = 0`
and `L u R = diag(1,1,1,0)`.
- Corollary J with `n = 4`, `k = 3`, `f = diag(1,1,1,0)` gives `f^((+)3) <~ I_8`. Since
  `I_9 <~ f^((+)3)`, `W` fails the rank condition and has no state.
- The configuration is impossible in every ring with the rank condition, weakly finite or not.
- The `1 x 1` collapse recorded on the (U1b) node is the case where the certified idempotent is `1`.

**Sharpness.** The bound is attained: on `F_3[C_3]` acting on itself, `u = x - 1` has cube zero and rank 2
of 3, and the regular representation gives an idempotent of rank 2 below `u` inside `M_3(F_3)`. Over a
division ring, Corollary J is the Jordan-form bound `rank(u) <= (k-1)n/k`.

**Consequences for the state upgrade.**
- **Outer s-rank.** For a state `s`, the outer s-rank of Proposition B,
  `rho^s(X) = sup s([f])` over idempotents `f <~ X`, obeys `rho^s(u) <= (k-1)n/k` whenever `u^k = 0`. So
  the Jordan upper bounds that a rank function imposes on order-three root elements `g - 1` in
  characteristic three (`N(g - 1) <= 2/3`) are already forced at the level of `K_0`.
- **What (U1b) must still supply.** Proposition B(4) leaves `N(g - 1)` free in `[0, 2/3]`. Corollary J
  shows that no single nilpotent can make these choices inconsistent. An inconsistency must involve a
  triangular step that mixes blocks, such as certificates for products of root elements from different
  root subgroups, for example `N_23 N_12`.
