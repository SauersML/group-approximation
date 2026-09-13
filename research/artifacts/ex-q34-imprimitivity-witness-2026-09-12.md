# Approximate systems of imprimitivity: coarse rigidity, standard-identity witnesses, quantitative rounding

Lane `ex-q34-collapse`, 2026-09-12.  This continues
`research/artifacts/ex-q34-frame-extraction-2026-09-12.md` (the soft-kernel
split) with finitary, dimension-free statements.  Everything here is proved in
full below.  Unreviewed by an independent verifier.

## 0. Summary

A family of unitaries on `C^d` has an *approximate system of imprimitivity*
when some orthogonal decomposition `C^d = ⊕_{i<=n} V_i` into equal-dimensional
subspaces (`dim V_i = k`) is approximately permuted.  This is the finitary
form of a block-monomial model and, by Mackey, the finitary form of an
induced representation.  The full masa is the case `k = 1` (monomial models,
induced from characters).

1. **Coarse rigidity (Lemma 1).**  If `u` approximately normalizes the abelian
   algebra `B = span{p_i}` of an equal-rank decomposition, with defect `delta`,
   then `u` is within `2 sqrt(3) delta` of `U(k) wr S_n` in normalized HS.  This
   holds uniformly in `k` and `n`.  It extends clause 1 of
   `diagonal-normalizer-rigidity` from the full masa to every equal-rank coarse
   frame, now with a block-monomial conclusion.
2. **Standard-identity witness (Lemma 2).**  In a regular block-monomial model
   with block size `k`, an element `g` whose conjugates `g_1..g_(2k)` have
   `(2k)!` pairwise distinct ordered products moves at least
   `c_k - O_k(delta)` of the blocks, with `c_k = 1/(8 k^2 (2k)!)`.  For
   `k = 1` the witness is one non-commuting conjugate and `c_1 = 1/16`.
3. **Quantitative rounding (Theorem 3).**  If every element of a window `E` has
   such a witness inside a window `F`, then regular block-monomial
   `(F, delta)`-models give `(E, eps)`-sofic approximations.  Their Hamming
   defect is `O_k(delta^2 log(1/eps))` and their separation is `1 - eps`.  The
   bounds are dimension-free and explicit.
4. **Asymptotic primitivity of the Leavitt units (Corollary 4).**  For
   microstates of `R^x`, with no trace condition, every approximately invariant
   equal-rank decomposition is asymptotically fixed blockwise on any fixed
   finite set of elements.

## 1. Coarse rigidity

Let `p_1..p_n` be orthogonal projections of rank `k` summing to `1` on
`C^(nk)`, `B = span{p_i}`, `E_B` the trace-preserving conditional expectation,
and `tr = Tr/(nk)`.  Put

```text
def_B(u) = sup{ ||u f u^* - E_B(u f u^*)||_2 : f = f^* in B, ||f|| <= 1 }.
```

**Lemma 1.**  If `def_B(u) <= delta` there is `W in U(k) wr S_n` (a permutation
`sigma` of the blocks and unitaries `w_i : ran p_i -> ran p_(sigma(i))`) with
`||u - W||_2 <= 2 sqrt(3) delta`.

*Proof.*  Put `A_(ji) = Tr(p_j u p_i u^*)/k`.  Then `A` is doubly stochastic,
since `sum_j A_ji = Tr(u p_i u^*)/k = 1` and `sum_i A_ji = Tr(p_j)/k = 1`.  For
`f = sum_i f_i p_i` one has `||f||_2^2 = (1/n) sum f_i^2` and
`E_B(u f u^*) = sum_j (A f)_j p_j`.  Since `E_B` is an orthogonal projection,

```text
||u f u^* - E_B(u f u^*)||_2^2 = ||f||_2^2 - (1/n) ||A f||^2 .
```

Average over uniformly random signs `f_i = ±1`.  This gives
`delta^2 >= 1 - (1/n) sum_(i,j) A_ji^2 >= 1 - (1/n) sum_i max_j A_ji`, because
`sum_j A_ji^2 <= max_j A_ji`.  Let `tau(i)` be a maximizing index.  Where
`max_j A_ji > 1/2`, `tau` is injective, since the columns of `A` sum to `1`.
Where `max_j A_ji <= 1/2`, the mass `1 - max` is `>= 1/2`, so those `i` have
density `<= 2 delta^2`.  Extend `tau` from the first set to a permutation
`sigma`.  Then

```text
||u - sum_i p_(sigma(i)) u p_i||_2^2 = (1/n) sum_i (1 - A_(sigma(i) i)) <= 3 delta^2 .
```

For each block `b_i = p_(sigma(i)) u p_i` (a contraction) take the polar unitary
`w_i`.  Since `0 <= |b_i| <= 1`,
`Tr((1-|b_i|)^2) <= Tr(1 - |b_i|^2) = k (1 - A_(sigma(i) i))`.  So
`W = sum_i w_i` satisfies `||sum_i b_i - W||_2^2 <= 3 delta^2`.  ∎

Products: `def_B(uv) <= def_B(u) + def_B(v)`, and
`def_B(u') <= def_B(u) + 2||u - u'||_2`.  So frame control on generators
propagates to a window of words with linear loss.

*Model tests.*  The Fourier-block unitary `⊕_j F_m` normalizes
`B = ℓ^∞_n ⊗ 1_m` exactly, and Lemma 1 correctly places it in `U(m) wr S_n`
with trivial permutation.  It is `sqrt 2` from the monomials, which is why
clause 1 of `diagonal-normalizer-rigidity` needs the full masa.  A Haar unitary
has `A` close to the flat matrix `J/n`, hence `def_B` close to `1` for `k << n`.

## 2. Block-monomial models and the Hamming skeleton

For `M = (u; sigma) in U(k) wr S_n` (acting by `e_i ⊗ v |-> e_(sigma(i)) ⊗ u_i v`)
the frame-extraction artifact proves

```text
d_H(sigma, sigma') <= ||M - M'||_2^2 / 2,     ||M - (u; id)||_2^2 = 2 d_H(sigma, id).   (HC)
```

A map `U : F -> U(k) wr S_n` is an `(F, delta)`-model when
`||U_x U_y - U_(xy)||_2 <= delta` whenever `x, y, xy in F` and
`||U_e - 1||_2 <= delta`.  It is *regular* when also `|tr U_w| <= delta` for
`w in F \ {e}`.  Then `||U_(x^(-1)) - U_x^*||_2 <= 2 delta` if `x, x^(-1) in F`,
and by (HC) the permutation parts are an `(F, 2 delta^2)`-almost action in
Hamming distance.

## 3. The standard-identity witness

`S_(2k)(x_1..x_(2k)) = sum_(pi in S_(2k)) sgn(pi) x_(pi 1) ... x_(pi 2k)` vanishes
on `M_k` (Amitsur--Levitzki), hence on block-diagonal matrices `(u; id)`.

**Lemma 2.**  Let `U` be a regular `(F, delta)` block-monomial model with block
size `k`, and let `g in F`.  Suppose `h_1..h_(2k) in F`, put
`g_i = h_i g h_i^(-1)`, and suppose the `(2k)!` words
`w_pi = g_(pi 1) ... g_(pi 2k)` are pairwise distinct.  Suppose `F` contains
`e`, every `h_i`, `h_i^(-1)`, `h_i g`, `g_i`, every prefix of every `w_pi`, every
`w_pi^(-1)` and every `w_pi^(-1) w_pi'`.  Then

```text
eta := d_H(sigma_g, id) >= 1/(8 k^2 (2k)!) - C_k delta.
```

*Proof.*  (i) *Conjugates are displaced as little as g.*  `U_(g_i)` is within
`4 delta` of `U_(h_i) U_g U_(h_i)^*`.  Its permutation part is within Hamming
`8 delta^2` of `sigma_(h_i) sigma_g sigma_(h_i)^(-1)`, whose displacement is `eta`.
So by (HC) the block-diagonal parts `D_i` satisfy
`||U_(g_i) - D_i||_2 <= rho := sqrt(2 eta + 16 delta^2)`.

(ii) *Upper bound.*  `S_(2k)(D_1..D_(2k)) = 0`.  Replacing each `D_i` by
`U_(g_i)` in a product of `2k` contractions costs `<= 2k rho` per term, and each
ordered product of the `U_(g_i)` is within `(2k-1) delta` of `U_(w_pi)`.  So

```text
|| sum_pi sgn(pi) U_(w_pi) ||_2 <= (2k)! (2k rho + 2k delta).
```

(iii) *Lower bound from the regular trace.*  Expanding the square,
`|| sum_pi sgn(pi) U_(w_pi) ||_2^2 = sum_(pi,pi') sgn(pi) sgn(pi') tr(U_(w_pi)^* U_(w_pi'))`.
The diagonal terms are `1`.  For `pi != pi'`, `tr(U_(w_pi)^* U_(w_pi'))` is within
`3 delta` of `tr U_(w_pi^(-1) w_pi')`, and that has modulus `<= delta`, since
`w_pi^(-1) w_pi' != e`.  So the square is `>= (2k)! - 4 ((2k)!)^2 delta`.

Combining (ii) and (iii) gives
`2k (rho + delta) >= (2k)!^(-1/2) (1 - 4 (2k)! delta)^(1/2)`.  With
`sqrt(1-x) >= 1-x` this gives
`rho >= (1 - 4 (2k)! delta)/(2k sqrt((2k)!)) - delta`, so
`eta = (rho^2 - 16 delta^2)/2 >= 1/(8 k^2 (2k)!) - C_k delta`.  ∎

For `k = 1`, `S_2(x, y) = xy - yx`, so the witness is a conjugate of `g` not
commuting with `g`.  Such a witness exists exactly when the normal closure of
`g` is nonabelian.  So Lemma 2 is the finitary form of "the monomial soft
kernel is an abelian normal subgroup".

*Model tests.*  In an abelian group every ordered product of the `g_i` is the
same element, so the lemma never applies.  That is correct: diagonal
random-character models are regular with zero displacement.  In `F_2 = <a, b>`
with `g = a`, `h = b`, a regular monomial model with `U_a` diagonal would make
`U_(bab^(-1))` diagonal, so it would commute with `U_a`, so
`tr U_([a, bab^(-1)])` would be close to `1`.  The lemma quantifies this.  The
constant `c_k` must tend to `0`: with unbounded `k`, `n` diagonal copies of any
microstate are block-monomial with zero displacement.

## 4. Quantitative rounding

**Theorem 3.**  Fix `k` and windows `E ⊆ F`.  Suppose every `g in E \ {e}` has a
witness as in Lemma 2 inside `F`.  Let `delta <= delta_k` be small enough that
Lemma 2 gives displacement `>= c_k/2`.  Then every regular `(F, delta)`
block-monomial model on `C^n ⊗ C^k` gives, for every `eps > 0`, maps
`s : E -> Sym(n^m)` with

```text
d_H(s_x s_y, s_(xy)) <= 2 m delta^2,   d_H(s_g, id) >= 1 - eps  (g != e),
m = ceil( 2 log(1/eps) / c_k ).
```

*Proof.*  Take the permutation parts `sigma` and their `m`-fold tensor powers
on `[n]^m`.  Hamming defects of products at most add over coordinates.  The
fixed-point density of `sigma_g^(⊗m)` is `(1 - d_H(sigma_g, id))^m`, which is at
most `(1 - c_k/2)^m <= eps`.  ∎

With Lemma 1 the hypothesis can be weakened to microstates approximately
normalizing an equal-rank coarse frame on generators: move them to
block-monomials at cost `2 sqrt(3) def` and propagate along words.  The result
is a dimension-free rounding theorem.  *Hyperlinear microstates that
approximately preserve an equal-rank coarse frame of bounded rank round to
sofic approximations of every witnessed window, at explicit cost.*  This is
the quantitative content of `block-monomial-hs-models-sofic-mod-amenable-soft-kernel`.

## 5. Asymptotic primitivity of the Leavitt unit group

**Corollary 4.**  Let `R = L_(F_2)(1,2)`.  For every finite `E ⊆ R^x` and
`eps > 0` there are a finite `F` and `delta > 0` with the following property.
Let `U : F -> U(d)` be any `(F, delta)`-almost multiplicative map, with no trace
condition and any `d`.  Let `C^d = ⊕_i V_i` be any equal-rank orthogonal
decomposition (any rank) with `def_B(U_x) <= delta` for `x in F`.  Then each
`g in E` maps all but an `eps`-fraction of the blocks `V_i` to themselves, up
to the Lemma 1 error.

*Proof.*  Lemma 1 moves `U` to a block-monomial `(F, O(delta))`-model whose
permutation parts form an `(F, O(delta^2))`-almost action.  The finitary clause
of `leavitt-unit-group-has-only-trivial-sofic-morphisms` states that at a
suitable scale `(F, delta)` every almost-multiplicative permutation model fixes
each element of `E` on all but an `eps`-fraction of points.  ∎

*Reading.*  Hilbert--Schmidt models of `R^x` are asymptotically primitive.  No
approximate system of imprimitivity is moved by any fixed element; in Mackey's
language no model is approximately induced with a nontrivial induction
skeleton.  Any hyperlinear construction for `R^x` must be asymptotically
primitive.  This is a checkable necessary condition on candidate models.
