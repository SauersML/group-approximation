# Finite-field Leavitt hosts: scalar-character splitting and cyclic-twist corners

Lane `gk-lp-hosts`, 2026-09-12. Supports the Cairn claims
`leavitt-unit-group-algebras-split-over-scalar-characters`,
`cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`,
`leavitt-visible-cyclic-corner-is-full-on-some-host` and
`some-finite-field-leavitt-unit-group-nonsurjunctive`, with their routes.

The question was which host `F_q[L_(F_q)(1,d)^x]` is most tractable for the linear route to a
Gottschalk counterexample. The answer recorded here: every host carries the same corner problem
and an image-level solution. The structure that made `F_3` work (a central sign and a diagonal unit
twisting the swap) exists on every host whose field contains a primitive `m`-th root of unity for
an admissible cycle length `m`. The problem is monotone in the field, so the roomiest statement is
the colimit over finite fields of one characteristic.

## 0. Setting

- `q = p^r` is a prime power and `d >= 2`.
- `L = L_(F_q)(1,d)`, `G = L^x`, `A = F_q[G]`, and `pi : A -> L` is the evaluation, the
  `F_q`-linear extension of the inclusion `G ⊂ L`. It is a unital ring homomorphism.
- For `m = 1 + j(d-1)` with `j >= 1`, `L` carries unital `m`-ary Leavitt families
  `s_1, ..., s_m, t_1, ..., t_m` (`t_i s_j = delta_ij`, `sum_i s_i t_i = 1`). Obtain one from the
  `d`-ary family by replacing a generator `s_k` with the `d` products `s_k s_1, ..., s_k s_d` (and
  `t_k` with `t_1 t_k, ..., t_d t_k`), `j` times. Call such `m` admissible.

## 1. Splitting over the scalar characters

**Theorem 1.** Let `Z = {lambda . 1 : lambda in F_q^x}`, a central cyclic subgroup of `G` of order
`q - 1`, which is prime to `p`. For `chi` in `X = Hom(Z, F_q^x)` put

    eps_chi = (1/(q-1)) sum_(lambda in F_q^x) chi(lambda)^(-1) [lambda].

1. The `eps_chi` are central orthogonal idempotents with sum `1`, so `A = prod_chi A_chi` with
   `A_chi = eps_chi A`. On `A_chi`, `[lambda]` acts as the scalar `chi(lambda)`.
2. Let `iota(lambda) = lambda`. Then `pi(eps_chi) = delta_(chi, iota)`, so `pi` factors through
   the Leavitt-visible factor `A_iota` and kills every other factor.
3. The trivial-character factor is `A_1 ~= F_q[G/Z]`.
4. If some factor contains `c, a` with `c a = eps_chi != a c`, then `C = c + (1 - eps_chi)` and
   `A' = a + (1 - eps_chi)` satisfy `C A' = 1 != A' C`. So `A` is not directly finite.
5. If `q > 2`, then `iota != 1`, and the augmentation `epsilon : A -> F_q` vanishes on `A_iota`,
   because `epsilon(eps_iota) = (1/(q-1)) sum_lambda lambda^(-1) = 0`. If `q = 2`, then `X` is
   trivial, `A = A_iota`, and the augmentation is visible on the Leavitt-visible factor.

*Proof.* `F_q^x` is cyclic of order `q - 1` and contains all `(q-1)`-th roots of unity, so `X` is
the full dual of `Z`. Orthogonality `sum_lambda chi(lambda)^(-1) psi(lambda) = (q-1) delta_(chi,psi)`
gives idempotency, orthogonality, the sum, and `[lambda] eps_chi = chi(lambda) eps_chi`. Centrality
holds because each `[lambda]` is central. For (2), `pi(eps_chi) = (1/(q-1)) sum_lambda
chi(lambda)^(-1) lambda = <chi, iota> = delta_(chi,iota)`. For (3), `A_1 = A / (([lambda] - 1)A)`,
which is `F_q[G/Z]`. Part (4) is direct: `C A' = c a + (1 - eps_chi) = 1`, and
`A' C = a c + (1 - eps_chi) != 1`. Part (5): `sum_(lambda in F_q^x) lambda^(-1) = 0` when `q > 2`. QED

For `q = 3` this is part 1 of `ternary-leavitt-swap-problem-splits-at-central-involution`.

## 2. Permutation units and image-level solutions on every host

**Theorem 2.** Let `m` be admissible with `p` not dividing `m`, and `s_i, t_i` an `m`-ary family.

1. For `sigma` in `S_m`, `u_sigma = sum_i s_(sigma(i)) t_i` is a unit, and `sigma -> u_sigma` is an
   injective homomorphism `S_m -> G`.
2. Let `H <= S_m` be transitive with `p` not dividing `|H|`, and `e_H = (1/|H|) sum_(sigma in H) [u_sigma]`,
   an idempotent of `A`. Put `b = sum_i s_i` and `c = (1/m) sum_i t_i`. Then `u_sigma b = b` for
   every `sigma`, so `pi(e_H) b = b`, and `c b = (1/m) sum_(i,j) t_i s_j = 1`. Hence

       c . pi(e_H) . b = 1   in L.

3. An admissible `m` prime to `p` exists for every `(q, d)`. If `p` does not divide `d - 1`, the
   values `1 + j(d-1)` run over all residues mod `p`. If `p` divides `d - 1`, every admissible `m`
   is `1 mod p`. Examples: `(q,d,m) = (2,2,3), (3,2,2), (4,2,3), (5,2,2), (5,2,4), (2,3,3)`.

*Proof.* `u_sigma u_tau = sum_(i,k) s_(sigma(i)) t_i s_(tau(k)) t_k = sum_k s_(sigma(tau(k))) t_k`,
and `u_sigma` has inverse `u_(sigma^(-1))`. It is injective because `t_(sigma(i)) u_sigma s_i = 1`.
The remaining identities are one-line computations with `t_i s_j = delta_ij`. Transitivity forces
`m` to divide `|H|`, so `p` does not divide `m`. QED

Take the cyclic group `H = C_m = <g>`, with `g = u_(1 2 ... m) = sum_i s_(i+1) t_i` (indices mod `m`).
It has order exactly `m`.

**A warning about characteristic two.** The order-three unit `g_0 = uv` of
`leavitt-corner-idempotent-unital-surjection` satisfies `g_0^2 + g_0 + 1 = 0` in `R = L_(F_2)(1,2)`,
so `pi(1 + g_0 + g_0^2) = 0`. The permutation unit `g` of a ternary family has
`pi(1 + g + g^2) = pi(e_(C_3))`, a nonzero idempotent equivalent to `1`. So `g` and `g_0` are not
conjugate in `G`, and the image equation above uses `g`, not `g_0`.

## 3. The cyclic twist

**Theorem 3.** Assume also that `m` divides `q - 1`. Let `zeta` in `F_q^x` have order `m`, and put

    delta = sum_i zeta^i s_i t_i   (a unit, with inverse sum_i zeta^(-i) s_i t_i).

1. `delta g delta^(-1) = zeta g`.
2. For `psi` in `Hom(C_m, F_q^x)` let `e_psi = (1/m) sum_(k=0)^(m-1) psi(g)^(-k) [g^k] eps_iota`.
   These are `m` orthogonal idempotents of `A_iota` with sum `eps_iota`, and `e_1 = e_H eps_iota`.
   Conjugation by `[delta]` sends `e_psi` to `e_(psi')` with `psi'(g) = psi(g) zeta^(-1)`. So it
   permutes them cyclically, they are pairwise equivalent, and

       A_iota ~= M_m(T),   T = e_1 A_iota e_1.

3. `A_iota` has no unital homomorphism to a nonzero commutative ring.
4. `c' e_1 b' = eps_iota` has a solution in `A_iota` iff `T` contains a unital `m`-pair Cohn family
   `gamma_i beta_j = delta_ij e_1` (`i, j = 1, ..., m`).
5. `pi` maps `T` onto the corner `pi(e_H) L pi(e_H)`, which is equivalent to `L` by Theorem 2 and so
   contains unital `m`-pair Cohn families.

*Proof.*
- (1): `delta g = sum_i zeta^(i+1) s_(i+1) t_i` and `g delta = sum_i zeta^i s_(i+1) t_i`, so
  `delta g = zeta g delta`, with `zeta` central.
- (2): in `A_iota`, `[zeta^k g^k] = zeta^k [g^k]`, because `[zeta^k]` acts as `zeta^k`. So
  `[delta] e_psi [delta]^(-1) = (1/m) sum_k psi(g)^(-k) zeta^k [g^k] eps_iota = e_(psi')`. The group
  algebra of `C_m` over `F_q` splits into the `m` isotypic idempotents because `p` does not divide
  `m` and `F_q` contains the `m`-th roots of unity. Orthogonal, pairwise equivalent idempotents summing
  to `1` give the matrix decomposition.
- (3): `M_m` with `m >= 2` has no such homomorphism.
- (4): in `M_m(T)`, `1 <= E_11` means `M_m(T) = P^m` embeds as a summand of `P = E_11 M_m(T)`. Under
  the Morita correspondence `P <-> T`, this is `T^m` embedding as a summand of `T`, that is, maps
  `f(x) = sum_j beta_j x_j` and `h(y) = (gamma_i y)_i` with `h f = id`, which is `gamma_i beta_j = delta_ij`.
- (5): `pi(e_1) = pi(e_H)`, and by Theorem 2 `c pi(e_H) b = 1` exhibits `pi(e_H) ~ 1`. QED

**Instances.**
- `(q, d, m) = (3, 2, 2)`: `g = s1 t0 + s0 t1 = w`, `zeta = -1`, `delta = s0 t0 - s1 t1`,
  `eps_iota = eps_-`, and (4) is part 3 of `ternary-leavitt-swap-problem-splits-at-central-involution`.
- `(q, d, m) = (4, 2, 3)`: `zeta = omega` in `F_4`, `g` is the 3-cycle of a ternary family and
  `delta = sum_i omega^i s_i t_i`. This is the characteristic-two analogue on the host
  `L_(F_4)(1,2)^x`, which contains `R^x`. Over `F_4` the augmentation vanishes on `A_iota`, while
  over `F_2` itself there is no twist and no splitting.
- `(q, d, m) = (5, 2, 4)`, `(7, 2, 3)`, `(7, 2, 6)`, `(5, 3, 3)` (3 is admissible for `d = 3`), and so on.

## 4. Ascent

**Proposition 4.**
1. *Along the field.* `L_(F_q)(1,d) ⊂ L_(F_(q^r))(1,d)` is a unital inclusion (base change along a
   field extension), so `G_q <= G_(q^r)` and `A(q) ⊂ A(q^r)`. The permutation units and `delta` are
   the same elements. If `c' e_1 b' = eps_iota(q)` in `A_iota(q)`, multiply by the central idempotent
   `eps_iota(q^r)`. In `A_iota(q^r)` each `[lambda]` with `lambda in F_q^x` acts as `lambda`, so
   `eps_iota(q) eps_iota(q^r) = eps_iota(q^r)`, and the products solve the equation over `F_(q^r)`.
2. *Along the arity.* Any one-sided pair in `F_q[L_(F_q)(1,2)^x]` stays a one-sided pair in
   `F_q[L_(F_q)(1,d)^x]` through the group inclusion of `leavitt-surjunctivity-tower`, since a group
   inclusion induces a unital algebra inclusion. The scalar characters do not match along this
   inclusion (a scalar `lambda` goes to `lambda p + (1 - p)`), so only plain non-direct-finiteness
   ascends here, not the corner form.
3. *Back to prime fields.* A pair over `F_(q^r)` makes `F_p[G_(q^r)]` not stably finite
   (`stable-finiteness-reduces-to-prime-field`), for the larger group `G_(q^r)`. It does not descend
   to `G_p`.
4. *Finite support.* A solution over the colimit `F_q[L_(Fbar_p)(1,d)^x]` has finite support, and
   each unit involved has finitely many coefficients, so the solution lives over one finite field.

So for fixed `(d, m)` the cyclic corner problem is monotone in `q`, and the roomiest form is the
colimit over the finite fields of characteristic `p` containing a primitive `m`-th root of unity.

## 5. Answers per host

- **The central splitting depends only on `q`:** `q - 1` factors, independent of `d`.
- **`p` divides `d - 1`:** every admissible `m` is `1 mod p`, so every transitive cyclic permutation
  corner is a `p'`-group and averages freely.
- **`p` odd, `d = 2`:** `m = 2` is admissible and divides `q - 1`, so every odd `q` carries the
  `F_3` structure verbatim, with `b = s0 + s1`, `c = (t0 + t1)/2`, `delta = s0 t0 - s1 t1`.
- **`d >= 3`:** `m = 2` is not admissible. The twist needs `m = 1 + j(d-1)` dividing `q - 1`, which a
  field extension supplies.
- **`q = 2`:**
  - There are no nontrivial scalar characters. The averaging corner `e_(C_3) = 1 + g + g^2` of a
    ternary permutation unit has augmentation `1`, lifted trace `1/3`, and the image equation of
    Theorem 2, but no matrix structure on `A`.
  - The twist and the vanishing augmentation first appear over `F_4`.
- **The `F_3` sign structure, explained:** `m = 2` divides `q - 1 = 2`, and `delta = s0 t0 - s1 t1`
  twists `w` by `-1`. The same happens over every `q = 1 mod m`.
- **What stays silent on `A_iota` under the twist:** augmentation (it vanishes), commutative
  quotients (there are none), and the lifted trace. The lifted trace forbids `e_1 ~ eps_iota` when
  `t_p(e_1) != 1`, but fullness only asks for `1 <= e_1`, which it does not forbid. Without the twist,
  `A_iota` can have one-dimensional representations through `K_1(L) = F_q^x/(F_q^x)^(d-1)` (when
  `q - 1` divides `d - 1`), so the twist is genuinely what removes them.

## 6. Where it dies

- **The lift:** find `b', c'` in `A_iota` lifting the image solution, or any solution of Theorem 3(4).
  Direct finiteness does not pass to quotients (`direct-finiteness-not-inherited-by-quotients`), so
  the image solution by itself transports nothing. This is exactly
  `leavitt-visible-cyclic-corner-is-full-on-some-host`.
- **The gate:** if `G_q` is `F_q`-linear sofic, then `A` is stably finite
  (`linear-sofic-group-algebra-is-stably-finite`) and every factor dies. Property (T) cannot decide
  that gate through rank rounding (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
- **No ranking of kernels:** no host has been shown to have a smaller or simpler evaluation kernel.
  What the survey shows is monotonicity in `q`, the uniform matrix form under the twist, and the one
  genuine difference at `q = 2`: the augmentation is visible there and there is no twist.
