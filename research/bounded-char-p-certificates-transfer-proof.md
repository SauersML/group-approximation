---
rg: 2
id: bounded-char-p-certificates-transfer-proof
kind: route
title: Fix the coincidence pattern by pigeonhole, pass to the ultraproduct group over the ultraproduct field of characteristic zero, and apply Kaplansky
target: bounded-char-p-certificates-transfer-to-characteristic-zero
requires: [c-linear-sofic-iff-bounded-dimension-large-characteristic]
---

Notation is as on `bounded-char-p-certificates-transfer-to-characteristic-zero`.

## 1. Uniform Kaplansky prime bound

**Kaplansky's theorem.** For every field `K` of characteristic `0`, every group `H` and every `k`, the ring
`M_k(K[H])` is directly finite: `ab = 1` implies `ba = 1`.
- For `K` a subfield of `C`, this is Kaplansky's trace argument: `e = ba` is an idempotent in `M_k(C[H])`, and
  `tau(e) = tau(ab) = k = tau(1)`, so the canonical trace gives `tau(1 - e) = 0`. The idempotent `1 - e` is similar to a
  projection `f` in `M_k` of the group von Neumann algebra, with `tau(f) = tau(1 - e) = 0`, so `f = 0` by faithfulness,
  and then `1 - e = 0`.
- For a general field of characteristic `0`, the entries of `a` and `b` generate a finitely generated field, which
  embeds in `C`.

**Step 1: the pattern.** Suppose, for a contradiction, that there are primes `p_1 < p_2 < ...`, fields `F_i` of
characteristic `p_i`, groups `G_i` and `(k, m)`-pairs `(a_i, b_i)` over `F_i[G_i]`. Pad the supports to exactly `m`
elements with zero coefficients, and write
`a_i = sum_(s=1..m) A_(i,s) g_(i,s)` and `b_i = sum_(t=1..m) B_(i,t) h_(i,t)`, with `A_(i,s)` and `B_(i,t)` in
`M_k(F_i)`.

The *pattern* of index `i` records:
- which of the elements `g_(i,s) h_(i,t)`, and `1`, are equal to each other;
- which of the elements `h_(i,t) g_(i,s)`, and `1`, are equal to each other.

There are finitely many patterns.

**Step 2: the ultraproduct.** Fix a non-principal ultrafilter `omega` on the index set. Put
- `K = prod_omega F_i`. It is a field (Łoś), and `n != 0` in `K` for every positive integer `n`, because
  `p_i > n` for almost all `i`. So `char K = 0`.
- `H = prod_omega G_i`, a group, with `g_s = [g_(i,s)]` and `h_t = [h_(i,t)]`.
- `A_s = [A_(i,s)]` and `B_t = [B_(i,t)]` in `M_k(K)`. Entrywise ultraproducts of matrices are well defined.
- `a = sum_s A_s g_s` and `b = sum_t B_t h_t` in `M_k(K[H])`.

In `H`, `g_s h_t = g_(s') h_(t')` iff this holds for `omega`-almost all `i`, and likewise for comparisons with `1` and
for the products `h_t g_s`. So the pattern of `(g_s, h_t)` in `H` is the pattern shared by `omega`-almost all indices.

**Step 3: `ab = 1`.** Let `C` be a class of pairs `(s, t)` with a common product `x_C = g_s h_t` in `H`. The coefficient
of `x_C` in `ab` is `sum_((s,t) in C) A_s B_t`, which is the ultraproduct of the matrices
`sum_((s,t) in C) A_(i,s) B_(i,t)`. For `omega`-almost all `i`, the set `C` is a class of the pattern of index `i`,
and this matrix is the coefficient of `x_(C,i)` in `a_i b_i = 1`: it is `I` if `x_C = 1` and `0` otherwise. Products
that do not occur have coefficient `0` on both sides. So `ab = 1` in `M_k(K[H])`.

**Step 4: `ba != 1`.** For each `i`, choose a witness that `b_i a_i != 1`:
- a class `D` of the `h g` part of the pattern (or the symbol `1` when `1` is not a product `h_(i,t) g_(i,s)`);
- an entry `(r, r')`;

such that the `(r, r')` entry of the coefficient of `x_(D,i)` in `b_i a_i` differs from the corresponding entry of the
identity. There are finitely many choices, so one choice holds for `omega`-almost all `i`.
- If the choice is the symbol `1`, then `1` is not among the products `h_t g_s` in `H`, so the coefficient of `1` in
  `ba` is `0`, and `ba != 1`.
- Otherwise, the `(r, r')` entry of the coefficient of `x_D` in `ba` is the ultraproduct of entries that differ from
  `delta_(x_D = 1) delta_(r r')` for almost all `i`, so it differs from it too.

So `ba != 1`. This contradicts Kaplansky's theorem for `M_k(K[H])`. Hence only finitely many primes carry
`(k, m)`-pairs, over all fields and groups of those characteristics together. Put `p_K(k, m)` equal to the largest of
them, or `1` if there is none.

**Step 5: computability.** Work in the two-sorted first-order language of a field, a group and the group operation.
- For each pattern `P` there is a sentence `phi_P` in this language, with `k^2 m` field variables for each of `a`
  and `b` and `m` group variables for each. It says that the group elements realise `P`, that the coefficient
  equations for `ab = 1` hold, and that some coefficient equation for `ba = 1` fails.
- Put `phi = OR_P phi_P`. A two-sorted structure satisfies `phi` iff its group algebra has a `(k, m)`-pair.
- Let `T_0` be the field axioms, the group axioms and the axioms `n != 0` for all positive integers `n`. By Step 4,
  `not phi` holds in every model of `T_0`. By the completeness theorem, `T_0` proves `not phi`.
- The proof uses only finitely many axioms `n != 0`, say those with `n <= N`, so `not phi` holds in every field of
  characteristic `p > N`. Enumerating proofs finds such an `N`. So some computable function bounds the least
  `p_K`, and the claim takes this computable bound as `p_K`.

In the Step 5 bullets, "by Step 4" means by Kaplansky's theorem: a model of `T_0` is a field of characteristic `0`
together with a group, so it satisfies `not phi`. Steps 1-4 are the semantic form of the same compactness argument.

**Marked groups.** A pair of size `k` supported in the ball of radius `r` over `F_p` is determined by the ball of radius
`2r` of the marked group together with finitely many coefficients. So the set of marked groups carrying such a pair is
clopen, and by Steps 1-4 it is empty once `p > p_K(k, |B_r|)`.

## 2. Uniform window bound

Fix `m` and `eps`. Up to isomorphism there are finitely many tables of size `m`.
- Let `T` be a table with a complex `(W, eps)`-model, of dimension `n`. Section 1 of
  `c-linear-sofic-iff-bounded-dimension-large-characteristic-proof` builds the constructible set `X_(T, eps, n)` over
  `Z`. Its definition uses only the table: the products `gh` inside `W` and which element is `1`.
  - `X(C)` is nonempty, so the image of `X` in `Spec Z` contains the generic point.
  - So the image contains all but finitely many primes `l`, and there is a model over some `F_(l^e)`.
- **Restriction of scalars.** Identify `F_(l^e)` with `F_l^e`. This gives an embedding of `GL_n(F_(l^e))` in
  `GL_(ne)(F_l)` that multiplies every rank by `e`. So normalised defects and separations are unchanged, and there is
  a model over `F_l`.
- Let `p_*(m, eps)` be the largest exceptional prime over the finitely many tables of size `m` that have complex
  models.

**Corollary.** Suppose a table `T` of `G` of size `m` has no `(W, eps)`-model over `F_p` for infinitely many `p`. Then
`T` has no complex model. By Lemma 3 of `root-splits-into-large-and-fixed-characteristic-witnesses-proof` over `C`, a
`C`-linear sofic group has complex models with separation `1/4` on every window, so `G` is not `C`-linear sofic.

For the growth statement, let `G` be in no `L_p` and `C`-linear sofic, and fix `eps`. Suppose that for infinitely many
`p` some table of size at most `m` has no `F_p`-model at `eps`. By pigeonhole one table fails for infinitely many
`p`. The corollary then contradicts `C`-linear soficity. So the least size of a failing table at `eps` tends to
infinity with `p`.

## 3. Consequences for component (b)

- **Growth of certificates.** If `(a_p, b_p)` is a `(k_p, m_p)`-pair over `F_p[G_p]`, then `p <= p_K(k_p, m_p)` by
  Section 1. Since `p_K` is finite at every argument, `max(k_p, m_p)` is unbounded along any infinite set of primes.
- **Integral designs.** A fixed pattern whose coefficients are integers, reduced mod `p` on groups `G_p`, is a
  `(k, m)`-pair of fixed size. So it works for at most the primes up to `p_K(k, m)`.
- **Formal strict pairs.** `formalizable-strict-pairs-certify-non-linear-soficity` converts a formalizable strict pair
  into a failure of stable finiteness, that is, a matrix pair. The bound applies to the size of that pair. A family of
  formal pairs whose linearizations have bounded size and matrix size serves only finitely many primes.

**What is not covered.** Certificates that never produce a matrix pair, for example metric window failures, are
controlled only through Section 2, and only for `C`-linear sofic witnesses.
