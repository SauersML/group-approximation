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

## 3. Proposition O: the outer s-rank is a rank function iff it is subadditive

Let `s` be a state on `(K_0(A), [A])`. The outer s-rank of Proposition B is

    rho^s(X) = sup { s([f]) : f idempotent, f <~ X }.

**Proposition O.**
1. `rho^s(0) = 0`, `rho^s(I_1) = 1`, and `rho^s(e) = s([e])` for every idempotent `e`. If `X` has `q`
   columns, `rho^s(X) <= q`.
2. `rho^s` is monotone for `<~`, so `rho^s(XY) <= min(rho^s(X), rho^s(Y))`.
3. `rho^s(X (+) Y) >= rho^s(X) + rho^s(Y)`.
4. `rho^s([[X, C], [0, Y]]) >= rho^s(X) + rho^s(Y)` for every `C`.
5. So `rho^s` is a Sylvester matrix rank function iff `rho^s(X (+) Y) <= rho^s(X) + rho^s(Y)` for all
   `X`, `Y`. It is then the smallest Sylvester rank function that agrees with `s` on idempotents.

*Proof.*
1. **Idempotent minors.** Let `f = L e R` with `e`, `f` idempotent. Put `alpha = e R f` and `beta = f L e`.
   Then `beta alpha = f (L e R) f = f`, and `e' = alpha beta = e R f L e` is an idempotent with
   `e' = e e' e`. So `[f] = [e'] <= [e]` and `s(f) <= s(e)`, with equality at `f = e`. If `X` has `q`
   columns, `f = (L X) R` gives `[f] <= q[A]` by the same computation. `f <~ 0` forces `f = 0`.
2. Minors compose.
3. `f <~ X` and `g <~ Y` give `f (+) g <~ X (+) Y`.
4. Lemma S with empty padding gives `f (+) g <~ [[X, C], [0, Y]]`. Take suprema.
5. The axioms in Section 1 of the kill-test artifact are `rk(0) = 0`, `rk(1) = 1`, the product bound,
   additivity on `(+)`, and the triangular bound. Parts 1–4 give all of them except additivity, and
   part 3 gives half of additivity. Minimality is item 2 of Proposition B: every Sylvester rank function
   `N` with `N(e) = s([e])` on idempotents satisfies `rho^s <= N`. ∎

**Use for (U1b).** A weakly finite image `W` of `S_-` carries a Sylvester rank function as soon as some
state on `W` has a subadditive outer s-rank. Subadditivity fails exactly when an idempotent below
`X (+) Y` beats every pair of idempotents below `X` and `Y`, which is the mixed shape again. No example
is known.

## 4. Theorem R: which states extend to rank functions

**Theorem R.** A state `s` on `(K_0(A), [A])` is the restriction to idempotents of a Sylvester matrix rank
function iff it is monotone for the triangular preorder on idempotents:

    f (+) K <=_T e (+) K   with e, f idempotent and K any matrix   implies   s([f]) <= s([e]).

Here `<=_T` is the preorder of Theorem 2.1 of the kill-test artifact, generated by minors and triangular
steps.

*Proof.*
1. **Only if.** A Sylvester rank function `N` extending `s` is monotone for `<=_T` and additive, so
   `s(f) + N(K) <= s(e) + N(K)`.
2. **The group.** As in steps 2–3 of that Theorem 2.1, let `G` be the Grothendieck group of matrices
   modulo mutual `<=_T`-domination, `P = { [N] - [M] : M <=_T N }`, and `u = [I_1]`, an order unit. In `G`,
   `[x] = [y]` iff `x (+) K ~ y (+) K` for some `K`.
3. **The subgroup.** Let `H` be the subgroup generated by classes of idempotents. Block sums of
   idempotents are idempotents, so every element of `H` is `[e] - [f]`. Put `phi([e] - [f]) = s(e) - s(f)`.
4. **Well defined.** If `[e] - [f] = [e'] - [f']`, then `e (+) f' (+) K ~ e' (+) f (+) K` for some `K`. The
   hypothesis, applied both ways to the idempotents `e (+) f'` and `e' (+) f`, gives
   `s(e) + s(f') = s(e') + s(f)`.
5. **Positive on `H ∩ P`.** Suppose `[e] - [f] = [N] - [M]` with `M <=_T N`, so `e (+) M (+) K ~ f (+) N (+) K`.
   Then `f (+) M (+) K <=_T f (+) N (+) K ~ e (+) M (+) K`. With `K' = M (+) K` the hypothesis gives
   `s(f) <= s(e)`.
6. **Extension.** A positive functional on a subgroup containing an order unit extends to a state on the
   preordered group. This is the lemma used in `anti-central-state-exists-iff-lifted-trace-relatively-positive`
   (Zorn's lemma, one element at a time; Goodearl's book, not re-read). For one new element `x`, the
   bounds `phi(h)/n` over `h <= n x` and `phi(h')/n'` over `n' x <= h'` satisfy `phi(h)/n <= phi(h')/n'`,
   because `n' h <= n n' x <= n h'`. Both sets are nonempty because `u` is an order unit, and any value
   between them keeps positivity.
7. **Rank function.** The extension `d: G -> R` is nonnegative on `P` with `d(u) = 1`. By Theorem 2.1(a)
   it is a Sylvester rank function, and `d([e]) = s([e])` on idempotents. ∎

**For (U1b).** `W` carries a Sylvester rank function iff some state on `(K_0(W), [W])` is monotone for
`<=_T` on idempotents. By `nilpotent-jordan-certificates-flatten-to-minors`, every Jordan certificate
`f^((+)k) <=_T I_((k-1)n)` is already a minor certificate, so it never violates monotonicity. A violation
needs a mixed triangular step.

## 5. Halving, and where this stops

**Halving (remark, not a theorem).** The unital homomorphism `M_2(S_-) -> S_-` of census Theorem E maps
minors to minors and triangular matrices to triangular matrices. So it transports certificates and
halves their sizes, which is how Theorem E shrinks the corner equation to size one. Separation, though,
is a property of which rows and columns the multipliers of a carried minor use. A ring homomorphism
applied entrywise keeps that pattern, so halving shrinks a mixed step without separating it. Jordan
certificates need no halving.

**Where it stops.**
- **Still not removable.** The triangular steps not covered by Lemma S are those whose carried idempotent
  minor mixes the two diagonal blocks with each other, or mixes both with one padding block.
- **In the gate.** The Frobenius step `2N(u^2) <= N(u) + N(u^3)` used for the bound in Proposition B(4) is
  removable, since Corollary J reaches the same bound `2/3` through separated nullity steps. The lower
  bounds for the two-root defect `N_23 N_12` come from arguments over products of different root elements.
  Nobody has checked whether their carried minors separate.
- **No calibration ring.** No mixed certificate over a ring with the rank condition is known, so no ring
  with the rank condition and without a Sylvester rank function is known either.
- **Two equivalent targets for (U1b).** Either show that some state on the weakly finite image is
  `<=_T`-monotone on idempotents (Theorem R), or find a state whose outer s-rank is subadditive
  (Proposition O). Both come down to mixed certificates.
