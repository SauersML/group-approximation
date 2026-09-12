# Inverse defects over the Leavitt evaluation: two normal forms

Lane `gk-kdf-structure`, 2026-09-12. Supports the Cairn claims
`binary-leavitt-algebra-is-purely-infinite-by-monomials`,
`leavitt-one-sided-pairs-are-unit-translates-of-s0-t0`,
`leavitt-inverse-defects-are-visible-or-invisible` and the open claims
`leavitt-evaluation-kernel-unitization-not-directly-finite`,
`leavitt-evaluation-kernel-unitization-directly-finite`,
`no-left-invertible-lift-of-s0-in-leavitt-group-algebra`,
`leavitt-unit-group-algebra-is-directly-finite`.

## Summary

Let `R = L_(F_2)(1,2)`, `Q = R^x`, `S = F_2[Q]`, `pi : S ->> R` the evaluation
(`leavitt-unit-group-algebra-surjects-onto-leavitt`), `K = ker pi`, and
`K^+ = F_2 1 + K`, a unital subring of `S` (`F_2 1` meets `K` in `0` because
`pi(1) = 1`).

Every one-sided inverse pair `b a = 1 != a b` in `S` can be translated by one
group element into exactly one of two normal forms:

* **(V) visible defect:** `pi(a) = s_0` and `pi(b) = t_0`;
* **(I) invisible defect:** `pi(a) = pi(b) = 1`, so `a, b` lie in `1 + K` and
  the defect `1 - ab` lies in `K`.

The case is decided by whether `pi(1 - ab)` is zero. Hence

```text
S is not directly finite
  <=>  (V*) some lift of s_0 is left invertible in S
   or  (I*) the unital subring K^+ is not directly finite.
```

(V*) is the existing claim `left-invertible-lift-of-s0-in-leavitt-group-algebra`.
Its route `leavitt-direct-finiteness-failure-from-left-invertible-lift` already
gave "(V*) implies not directly finite". What is new is the converse for visible
defects: a direct-finiteness failure whose defect survives evaluation is always
a lift of `s_0`, and its partner can be taken over `t_0`. So the Kaplansky
question for `Q`, and by `leavitt-stable-finiteness-equals-direct-finiteness`
and `stable-finiteness-failure-refutes-surjunctivity` the linear case of
Gottschalk's conjecture for `Q`, is exactly two lifting problems.

The only input beyond the Leavitt relations is an elementary monomial form of
pure infiniteness for `R` (Lemma 1), proved here in full.

## 0. Conventions

`R` is the unital `F_2`-algebra on `s_0, s_1, t_0, t_1` with

```text
t_i s_j = delta_ij,        s_0 t_0 + s_1 t_1 = 1.
```

For a finite word `alpha = alpha_1 ... alpha_k` over `{0,1}` write
`S[alpha] = s_(alpha_1) ... s_(alpha_k)` and
`T[beta] = t_(beta_l) ... t_(beta_1)`, the convention of
`experiments/nonsofic-certificates/README.md`. The monomials
`S[alpha] T[beta]` span `R`.

**(M1)** Let `beta, gamma` be words. If `|gamma| <= |beta|`, then
`T[beta] S[gamma] = T[beta']` when `beta = gamma beta'`, and `0` otherwise. If
`|gamma| >= |beta|`, then `T[beta] S[gamma] = S[gamma']` when
`gamma = beta gamma'`, and `0` otherwise.

*Proof.* `T[beta] S[gamma] = t_(beta_l) ... t_(beta_1) s_(gamma_1) ... s_(gamma_k)`.
The innermost pair `t_(beta_1) s_(gamma_1)` equals `delta`, and induction
cancels one letter at a time.

**(M2)** For every `m >= 0`, `sum_(|gamma| = m) S[gamma] T[gamma] = 1`.

*Proof.* Induction on `m`, using `S[gamma i] T[gamma i] = S[gamma] s_i t_i T[gamma]`
and `s_0 t_0 + s_1 t_1 = 1`.

**(M3)** The words `S[alpha]`, `alpha` in `{0,1}^*`, are linearly independent in `R`.

*Proof.* Let `X` be the set of one-sided infinite binary sequences and
`V = F_2^(X)` the vector space with basis `X`. Define `s_i(x) = i x`,
`t_i(i x) = x` and `t_i(j x) = 0` for `j != i`. These operators satisfy the
Leavitt relations: `t_i s_j = delta_ij`, and `s_0 t_0 + s_1 t_1` fixes every
sequence. So they define a representation of `R` in which `S[alpha]` sends
`x` to `alpha x`. Choose `x` not eventually periodic, for instance
`0 1 00 11 000 111 ...`. If `alpha x = alpha' x` with `|alpha| < |alpha'|`,
then `alpha' = alpha alpha''` and `x = alpha'' x`, which makes `x` periodic.
So the vectors `S[alpha] x` are distinct basis vectors of `V`, and a nontrivial
relation among the `S[alpha]` would be a nontrivial relation among distinct
basis vectors.

## 1. Monomial pure infiniteness

**Lemma 1.** For every nonzero `x` in `R` there are words `alpha*, gamma, w`
with

```text
T[w] T[alpha*] x S[gamma] S[w] = 1.
```

*Proof.* Write `x` as a finite sum of monomials `S[alpha] T[beta]` and let
`m` be the largest `|beta|` that occurs. By (M2),
`x = sum_(|gamma| = m) x S[gamma] T[gamma]`, so `y = x S[gamma] != 0` for some
`gamma` of length `m`. By (M1) every `S[alpha] T[beta] S[gamma]` is `0` or a word
`S[alpha gamma']`, so `y` is a sum of words. By (M3), `y = sum_(alpha in A) S[alpha]`
for a nonempty finite set `A` of distinct words.

Let `alpha*` in `A` have maximal length. By (M1),

```text
z := T[alpha*] y = 1 + sum_(delta in D) T[delta],
```

where `D` is the set of nonempty words `delta` with `alpha* = alpha delta` for
some `alpha` in `A`. The words in `D` have distinct lengths, so nothing cancels.
If `D` is empty we are done with `w` empty. Otherwise let
`L >= max |delta|` and `w = 0 1^L`. For `delta` in `D`, `|delta| < |w|`, so by (M1)
`T[delta] S[w]` is `0` unless `delta` is a prefix of `w`. In that case
`delta = 0 1^i` with `0 <= i <= L - 1` and `T[delta] S[w] = S[1^(L-i)]`. Thus

```text
T[w] z S[w] = T[w] S[w] + sum T[w] S[1^(L-i)] = 1 + 0,
```

because `1^(L-i)` is a nonempty word beginning with `1`. It is shorter than `w`
and is not a prefix of `w`, which begins with `0`, so (M1) gives `0`. Hence
`T[w] T[alpha*] x S[gamma] S[w] = T[w] z S[w] = 1`.

This is the monomial form of pure infiniteness of the Leavitt algebra (compare
Ara--Goodearl--Pardo, whose Theorem 4.2 is imported in
`agp-purely-infinite-simple-k1-citation`). Nothing below uses more than Lemma 1.

## 2. Defect idempotents of R are equivalent to one

**Lemma 2.** Let `alpha, beta` in `R` with `beta alpha = 1 != alpha beta`, and put
`p = 1 - alpha beta`. Then `pR ~= R_R` as right modules. Equivalently there are
`x` in `pR s_1 t_1` and `y` in `s_1 t_1 R p` with

```text
x y = p,        y x = s_1 t_1.
```

*Proof.* `p` is a nonzero idempotent. By Lemma 1 there are `mu, nu` with
`mu p nu = 1`. Put `a = p nu` and `b = mu p`, so `b a = 1`, and `q = a b`. Then `q`
is an idempotent with `pq = qp = q`, and `r = p - q` is an idempotent orthogonal
to `q`. Left multiplication by `a` is an isomorphism `R -> qR` with inverse left
multiplication by `b`, so

```text
pR = qR (+) rR ~= R (+) rR.
```

The Leavitt relations give `R ~= R (+) R` (`u -> (t_0 u, t_1 u)`, inverse
`(u_0, u_1) -> s_0 u_0 + s_1 u_1`). Hence

```text
pR (+) R ~= R (+) R (+) rR ~= R (+) rR ~= pR.
```

On the other side `R = alpha beta R (+) pR`, and left multiplication by `alpha`
is an isomorphism `R -> alpha beta R` with inverse left multiplication by `beta`.
So `R ~= R (+) pR`. Combining,

```text
pR ~= pR (+) R ~= R (+) pR ~= R.
```

An isomorphism `phi : R -> pR` is left multiplication by `x_1 = phi(1)` in `pR`.
Its inverse, extended by zero on `(1-p)R`, is left multiplication by some `y_1`
in `Rp`, with `y_1 x_1 = 1` and `x_1 y_1 = p`. Composing with the equivalence
`t_1 s_1 = 1`, `s_1 t_1 = s_1 t_1` gives `x = x_1 t_1` and `y = s_1 y_1`:
`x y = x_1 y_1 = p` and `y x = s_1 y_1 x_1 t_1 = s_1 t_1`.

## 3. One-sided pairs of R form one orbit under the unit group

**Theorem 3.** Let `alpha, beta` in `R` with `beta alpha = 1 != alpha beta`. There
is a unit `w` in `Q = R^x` with

```text
w alpha = s_0,        beta w^(-1) = t_0.
```

*Proof.* Let `p = 1 - alpha beta` and `p' = s_1 t_1`, and let `x, y` be as in
Lemma 2. Put

```text
w = s_0 beta + y,        w' = alpha t_0 + x.
```

Four vanishings are used:

* `beta p = beta - beta alpha beta = 0` and `p alpha = alpha - alpha beta alpha = 0`;
* `t_0 p' = t_0 s_1 t_1 = 0` and `p' s_0 = s_1 t_1 s_0 = 0`.

Since `x = p x p'` and `y = p' y p`:

```text
w w' = s_0 beta alpha t_0 + s_0 beta x + y alpha t_0 + y x
     = s_0 t_0 + 0 + 0 + s_1 t_1 = 1,
w' w = alpha t_0 s_0 beta + alpha t_0 y + x s_0 beta + x y
     = alpha beta + 0 + 0 + p = 1.
```

So `w` is a unit with inverse `w'`. Finally
`w alpha = s_0 beta alpha + y alpha = s_0` and
`beta w' = beta alpha t_0 + beta x = t_0`.

So every one-sided inverse pair of `R` is `(w^(-1) s_0, t_0 w)` for some `w` in `Q`.

## 4. Normal forms of inverse defects in S

**Theorem 4.** Let `a, b` in `S` with `b a = 1 != a b`, and put `delta = 1 - ab`, a
nonzero idempotent.

* **(V)** If `pi(delta) != 0`, let `w` be the unit of Theorem 3 for
  `(pi(a), pi(b))`, and put `a' = [w] a`, `b' = b [w^(-1)]`. Then
  `b' a' = 1 != a' b'`, `pi(a') = s_0` and `pi(b') = t_0`.
* **(I)** If `pi(delta) = 0`, then `r = pi(a)` is a unit of `R` with inverse
  `pi(b)`. Put `a' = [r^(-1)] a`, `b' = b [r]`. Then `b' a' = 1 != a' b'`,
  `pi(a') = pi(b') = 1`, and `1 - a' b' = [r^(-1)] delta [r]` lies in `K`.

*Proof.* In both cases `b' a' = b a = 1`, and `a' b'` is a conjugate of `ab` by a
unit of `S`, hence `!= 1`. In case (V), `pi(b) pi(a) = 1` and
`pi(a) pi(b) = 1 - pi(delta) != 1`, so Theorem 3 applies and gives the images.
In case (I), `pi(a) pi(b) = 1 = pi(b) pi(a)`, so `r` is in `Q`.

**Corollary 5.** `S` fails direct finiteness if and only if

* (V*) there are `a, b` in `S` with `pi(a) = s_0`, `pi(b) = t_0` and `b a = 1`; or
* (I*) there are `u, v` in `K` with `(1 + v)(1 + u) = 1 != (1 + u)(1 + v)`, that
  is, `K^+` is not directly finite.

(V*) is equivalent to `left-invertible-lift-of-s0-in-leavitt-group-algebra`. If
`pi(a) = s_0` and `b a = 1`, then `pi(b) = t_0 + gamma t_1` with
`gamma = pi(b) s_1`. The element `v = 1 + s_0 gamma t_1` of `Q` is an involution,
because `t_1 s_0 = 0` and the characteristic is two. It satisfies `v s_0 = s_0`
and `pi(b) v = t_0`. So `[v] a` and `b [v]` form a pair over `(s_0, t_0)`.

*Proof.* If `S` is not directly finite, Theorem 4 puts a witness in form (V) or
(I). Conversely, a pair over `(s_0, t_0)` has `ab != 1` by the argument of
`leavitt-direct-finiteness-failure-from-left-invertible-lift`: applying `pi` to
`ab = 1` would make `s_0` a unit of `R`. A failure in the unital subring `K^+`
is a failure in `S`.

## 5. What a defect cannot be

**Proposition 6.** For every group `G` and field `k`, the defect
`delta = 1 - ab` of a pair `b a = 1 != a b` in `k[G]` is never Murray--von Neumann
equivalent to `1`, although `k[G] ~= k[G] (+) delta k[G]`.

*Proof.* Suppose `d c = 1` and `c d = delta`. Then `delta c = c` and `d delta = d`,
so `b c = b delta c = 0` (as `b delta = 0`), `d a = d delta a = 0` (as
`delta a = 0`), and `ab + cd = 1`. Thus `a, c, b, d` form a unital binary Leavitt
family in `k[G]`. Applying the augmentation gives `eps(b) eps(a) = 1`,
`eps(d) eps(c) = 1` and `eps(b) eps(c) = 0` in the field `k`, which is
impossible. This is the field form of `augmentation-blocks-unital-leavitt-family`.

In case (V), `pi(delta) = s_1 t_1` is equivalent to `1` in `R`, but the
equivalence cannot lift. A witness to (V*) lifts the Leavitt pair `(s_0, t_0)`
exactly, and it cannot be completed to a lift of the whole family
`(s_0, s_1, t_0, t_1)`. In case (I), `delta k[G]` becomes zero after base change
along `pi`.

## 6. Attempts on the invisible problem (I*)

* **Radical perturbation.** Dead. `K` contains the idempotent
  `z = [1] + [g] + [g^2]` (`leavitt-evaluation-kernel-hits-augmentation-one`),
  and `1 + z = [g] + [g^2]` is a nonzero idempotent different from `1`, so `1 + K`
  contains non-units and `K` is not in the Jacobson radical.
* **Separated powers.** Dead. `K` contains infinitely many nonzero idempotents
  (`leavitt-recursive-kernel-idempotents`), and an idempotent lies in every
  power `K^m`, so the mechanism of
  `residually-p-kernels-preserve-modular-stable-finiteness` cannot run.
* **Detection by directly finite quotients.** Every ring homomorphism to a
  directly finite ring kills every defect. Finite-dimensional representations
  of `S` over fields factor through the augmentation, because `Q` is finitely
  generated, simple and infinite (Theorem A of `non_mf_groups_exist.tex`) and
  finitely generated linear groups are residually finite. They kill all of the
  augmentation ideal, hence detect nothing inside `K n ker(eps)`, where an
  invisible defect lives: `eps(1 - ab) = 0`.
* **Transport along the recursive corner.** The embedding
  `lambda : S -> fSf` of `leavitt-primitive-corner-recursive-extension`
  satisfies `rho lambda = pi`. It carries invisible pairs to invisible pairs of
  the corner, and visible to visible, so it converts neither problem into the
  other.
* **Converting between the two problems.** Neither direction is known. Module
  form: (V*) asks for a nonzero projective `P` with `S (+) P ~= S` and
  `P (x)_S R ~= R`; (I*) asks for one with `P (x)_S R = 0`. Direct sums of
  copies stay in their class, since `R (+) R ~= R`.

## 7. Scope

Nothing here decides either problem, and nothing is claimed about whether
`S` is directly finite. The content is exact normalization: a search or a proof
may fix `pi(a) = s_0` and `pi(b) = t_0`, or `pi(a) = pi(b) = 1`, and every other
evaluation pattern of a witness is a translate by one element of `Q`. For the
positive direction, `S` is directly finite exactly when both problems fail.
