# The unit group algebra of the binary Leavitt algebra embeds in a corner of its evaluation kernel

Lane `gk-l2-visible`, 2026-09-12. Supports the Cairn claims
`leavitt-unit-group-algebra-embeds-in-kernel-corner`,
`leavitt-kaplansky-failures-have-invisible-witnesses` and
`leavitt-matrix-units-lift-into-finite-subgroup-algebra`, and the routes
`kernel-unitization-failure-from-group-algebra-failure`,
`leavitt-df-from-kernel-unitization-df` and `no-s0-lift-from-kernel-unitization-df`.

## Summary

Let `R = L_(F_2)(1,2)`, `G = R^x`, `S = F_2[G]`, `pi : S ->> R` the evaluation
(`leavitt-unit-group-algebra-surjects-onto-leavitt`), `K = ker pi` and
`K^+ = F_2 1 + K`.

The normal forms of `leavitt-inverse-defects-are-visible-or-invisible` split a
direct-finiteness failure of `S` into a visible problem (V*), a left-invertible lift
of `s_0`, and an invisible problem (I*), a failure inside `K^+`. That artifact
records that no conversion between the two problems was known. This note proves one
direction, in a stronger form:

```text
S is directly finite   <=>   K^+ is directly finite,
```

and every one-sided pair of `S`, visible or not, maps to an invisible pair under an
explicit injective unital multiplicative map `Phi : S -> K^+`. So (V*) implies (I*),
the invisible problem is the whole Kaplansky question for `G`, and (V*) is the
strictly more demanding form. The converse (I*) => (V*) is not known.

The mechanism is a corner of the kernel that contains a copy of `S`. The scalar copy
`delta(G)` of `G` commutes with a constant copy of `S_3`, and the complementary
idempotent of the `S_3` block over `1` lies in the kernel.

## 0. Conventions

`R` is the unital `F_2`-algebra on `s_0, s_1, t_0, t_1` with `t_i s_j = delta_ij`
and `s_0 t_0 + s_1 t_1 = 1`. The map

```text
Theta_2 : M_2(R) -> R,     Theta_2((a_ij)) = sum_(i,j) s_i a_ij t_j
```

is a unital algebra isomorphism with inverse `x |-> (t_i x s_j)`. Put

```text
u = 1 + s_0 t_1 = Theta_2([[1,1],[0,1]]),   v = 1 + s_1 t_0 = Theta_2([[1,0],[1,1]]),
g = uv = Theta_2([[0,1],[1,1]]),            w = uvu = vuv = Theta_2([[0,1],[1,0]]),
delta(q) = s_0 q t_0 + s_1 q t_1 = Theta_2(q I_2).
```

`H = <u, v>` is `Theta_2(GL_2(F_2))`, a copy of `S_3`, with `g` of order 3 and
`g^2 = vu`.

## 1. Two commuting copies

**Lemma 1.** `delta : G -> G` is an injective group homomorphism, `delta(G)`
commutes elementwise with `H`, and `delta(G) n H = {1}`. Hence
`delta(G) x H -> G`, `(p, h) |-> p h`, is an injective homomorphism, and

```text
F_2[delta(G)] (x) F_2[H]  ~=  F_2[delta(G) x H]  <=  S.
```

*Proof.* `delta` is `Theta_2` composed with `q |-> q I_2`, which is multiplicative
and injective, and `t_0 delta(q) s_0 = q` recovers `q`. For `C` in `GL_2(F_2)`, the
matrices `q I_2` and `C` commute in `M_2(R)`, because the entries of `C` are central
scalars. So `delta(q) Theta_2(C) = Theta_2(C) delta(q)`. If `delta(q) = Theta_2(C)`,
then `q I_2 = C`. So `C` is diagonal with both diagonal entries equal to `q`, and `q`
lies in `F_2^x = {1}`. The group algebra of a subgroup is a subalgebra, and the group
algebra of a direct product is the tensor product. (This is the construction of
`leavitt-matrix-amplification-in-unit-group-algebra`, restated with its proof.)

## 2. An idempotent of the kernel

**Lemma 2.** `z = [1] + [g] + [g^2]` is an idempotent of `F_2[H]`, `e = 1 + z = [g] + [g^2]`
is the complementary idempotent, `z e = e z = 0`, `pi(z) = 0` and `pi(e) = 1`.

*Proof.* The powers of `g` commute, so `z^2 = [1] + [g^2] + [g^4] = z` in
characteristic two. Then `e = 1 - z` is idempotent and orthogonal to `z`. For the
evaluation, `pi` restricted to `F_2[H]` is `Theta_2` of the natural representation
`F_2[GL_2(F_2)] -> M_2(F_2)`, and

```text
I + [[0,1],[1,1]] + [[1,1],[1,0]] = [[0,0],[0,0]],
```

so `pi(z) = 0` and `pi(e) = 1`. (This is the idempotent witness recorded in
`leavitt-evaluation-kernel-hits-augmentation-one`.)

## 3. The padded corner embedding

**Theorem 3.** The map

```text
j : S -> z S z,     j(x) = delta(x) z
```

is an injective unital ring homomorphism, where `z` is the identity of `zSz`, and
`zSz` is contained in `K`. Consequently

```text
Phi : S -> K^+,     Phi(x) = delta(x) z + e
```

is injective and multiplicative with `Phi(1) = 1`. For every one-sided pair
`b a = 1 != a b` in `S`, the elements `alpha = Phi(a)` and `beta = Phi(b)` satisfy

```text
beta alpha = 1,   alpha beta != 1,   pi(alpha) = pi(beta) = 1,
1 - alpha beta = delta(1 - ab) z  in  K.
```

*Proof.* Here `delta` also denotes the linear extension `S -> F_2[delta(G)]`, an
injective algebra homomorphism. Because `delta(S)` commutes with `z`,
`j(x) j(y) = delta(x) z delta(y) z = delta(xy) z^2 = j(xy)`, and `j` is additive with
`j(1) = z`. It is injective: `delta(x) z = 0` is `delta(x) (x) z = 0` in the tensor
decomposition of Lemma 1, so `delta(x) = 0` and `x = 0`. Since `K` is a two-sided ideal
containing `z`, `zSz` lies in `K`.

For `Phi`, use `z e = e z = 0` and `delta(S) e = e delta(S)`:

```text
Phi(x) Phi(y) = delta(x) z delta(y) z + delta(x) z e + e delta(y) z + e e = delta(xy) z + e = Phi(xy),
```

and `Phi(1) = z + e = 1`. Also `Phi(x) - 1 = delta(x) z + e - (z + e) = (delta(x) - 1) z`
lies in `K`, so `Phi(S)` is contained in `K^+`. Injectivity of `Phi` follows from that
of `j`.

Given `b a = 1`, multiplicativity gives `beta alpha = Phi(ba) = Phi(1) = 1`. If
`alpha beta = 1`, then `Phi(ab) = Phi(1)`, so `ab = 1`, a contradiction. The
evaluations are `pi(Phi(x)) = pi(delta(x)) pi(z) + pi(e) = 0 + 1 = 1`. The defect is
`1 - Phi(ab) = (z + e) - (delta(ab) z + e) = delta(1 - ab) z`, which lies in `Sz` and
so in `K`.

**Remark.** `Phi` is not additive (`Phi(x + y) = Phi(x) + Phi(y) + e`). The ring
homomorphism is `j`; `Phi` pads it by the complementary idempotent, as in every corner
padding of this region.

## 4. Consequences for the two lifting problems

**Corollary 4.**

1. `S` is directly finite if and only if `K^+` is directly finite.
2. A witness to `left-invertible-lift-of-s0-in-leavitt-group-algebra` (V*) yields a
   witness to `leavitt-evaluation-kernel-unitization-not-directly-finite` (I*).
3. `leavitt-evaluation-kernel-unitization-directly-finite` alone implies both
   `leavitt-unit-group-algebra-is-directly-finite` and
   `no-left-invertible-lift-of-s0-in-leavitt-group-algebra`. The existing route into
   the positive root needed both negations.

*Proof.* (1) `K^+` is a unital subring of `S`, so a failure in `K^+` is a failure in
`S`. Theorem 3 gives the converse. (2) A (V*) witness has `a b != 1`: applying `pi` to
`a b = 1` would make `s_0` a unit of `R`, which it is not
(`leavitt-direct-finiteness-failure-from-left-invertible-lift`). So it is a
direct-finiteness failure of `S`, and Theorem 3 converts it. (3) is the contrapositive
of (1) and (2).

**What this changes.** The normal-form artifact names two independent problems. After
Corollary 4 they are nested. The invisible problem is equivalent to the Kaplansky
question for `G`, and the visible problem is a sufficient, strictly more specific form,
the one that reads the four-site rule of
`leavitt-kernel-annihilator-strict-self-embedding` as a full-shift automaton. Searches
and proofs aimed at a counterexample may fix the invisible normal form with no loss.
Proofs aimed at direct finiteness need only exclude invisible pairs.

**What it does not give.** A conversion (I*) => (V*). The kernel defect
`delta(1 - ab) z` is killed by `pi`, and nothing here moves an invisible defect to a
visible one.

## 5. Lifted matrix units

**Lemma 5.** In `F_2[H]` put

```text
f_11 = [1] + [u] + [v] + [g],     f_22 = [1] + [u] + [v] + [g^2],
f_12 = [g] + [g^2] + [v] + [w],   f_21 = [g] + [g^2] + [w] + [u].
```

Then `f_ij f_kl = delta_jk f_il`, `f_11 + f_22 = e`, `e` is central in `F_2[H]`, and
`pi(f_ij) = s_i t_j`.

*Proof.* `e` is `1` plus the class sum of the 3-cycles, hence central. The algebra
`F_2[S_3]` is the product of its principal block and the block of the natural
2-dimensional representation `rho : F_2[H] -> M_2(F_2)`. The latter is projective
(dimension 2, the 2-part of 6), so its block is `e F_2[H] ~= M_2(F_2)`, with `rho`
restricting to an isomorphism. Hence `f_ij := x_ij e` for any `x_ij` with
`rho(x_ij) = E_ij` is a system of matrix units summing to `e`. Take
`x_11 = 1 + u + v + g`, `x_22 = u + v + g`, `x_12 = 1 + u`, `x_21 = 1 + v`. Direct
evaluation in `M_2(F_2)` gives `E_11, E_22, E_12, E_21`. Multiplying out with
`ug = v`, `ug^2 = w`, `vg = w`, `vg^2 = u` and `g^3 = 1` gives the displayed supports.
For example `f_22 = (u + v + g)(g + g^2) = v + w + w + u + g^2 + 1`. Finally
`pi(f_ij) = Theta_2(E_ij) = s_i t_j`.

These are finite, explicit lifts of the Leavitt matrix units. With the scalar copy they
realize `M_2(S)` inside `eSe`, compatibly with `Theta_2`:
`pi(delta(x) f_ij) = s_i pi(x) t_j`. The identity they sum to is `e`, not `1`, which is
consistent with `augmentation-blocks-unital-leavitt-family`.

## 6. Scope and other coefficient fields

* The same argument runs over any field `k` of characteristic not `3`, for `L_k(1,2)`.
  Use the averaging idempotent `(1 + g + g^2)/3` of the constant `C_3`: its natural
  representation has no nonzero fixed vector, so it evaluates to `0`, and the constant
  and scalar copies still commute and meet trivially.
* Over `F_3` the level-one trick is unavailable. A subgroup of `GL_2(F_3)` of order
  prime to 3 is a 2-group. If its order is at least 4 it contains `-I`: an element of
  order 4 squares to `-I`, and two commuting non-scalar involutions `diag(1,-1)`,
  `diag(-1,1)` multiply to `-I`. A single non-scalar involution has eigenvalue `1`, so it
  has a nonzero fixed vector. And `-I = delta(-1)` lies in the scalar copy. The ternary
  lanes also use the central splitting at `-1`
  (`ternary-leavitt-swap-problem-splits-at-central-involution`).
* **Correction (2026-09-12): the transfer does hold over `F_3`, at level two.**
  - Use `Theta_4 : M_4(R) -> R`, with scalar copy `sum_(|alpha| = 2) S[alpha] q T[alpha]`.
  - Take a cyclic subgroup of order 5 in `GL_4(F_3)` acting irreducibly (5 is a primitive
    prime divisor of `3^4 - 1`). It has no nonzero fixed vector, meets the scalars
    `{I, -I}` only in `I`, and its averaging idempotent is killed by the natural
    representation.
  - The general criterion, for every finite field and every type `(1,d)`, is
    `leavitt-invisible-half-universal-over-every-finite-field` (lane `gk-l2-invisible`).
    The level-one sentence above limits only the level-one construction.
* Nothing here decides (V*), (I*) or direct finiteness of `S`.
