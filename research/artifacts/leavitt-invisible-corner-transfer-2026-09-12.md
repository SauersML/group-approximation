# Independent derivation: every Kaplansky pair over the Leavitt unit group becomes an invisible pair

Lane `gk-l2-invisible`, 2026-09-12. This is an independent re-derivation of the theorem
that `gk-l2-visible` lands as the canonical claims
`leavitt-unit-group-algebra-embeds-in-kernel-corner` and
`leavitt-kaplansky-failures-have-invisible-witnesses`, with artifact
`research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md`. Both lanes found the
same construction within minutes of each other; the canonical ids are theirs. This
artifact supports the claim `leavitt-invisible-half-universal-over-every-finite-field` and its
route `leavitt-invisible-half-universal-over-every-finite-field-proof` (Sections "General
criterion" and "Existence over every finite field"), the route
`kernel-unitization-df-from-unit-group-algebra-df`, and the
Attempts lines on `leavitt-evaluation-kernel-unitization-not-directly-finite`,
`leavitt-evaluation-kernel-unitization-directly-finite` and
`leavitt-inverse-defects-are-visible-or-invisible`.

## Notation

`R = L_(F_2)(1,2)`, `Q = R^x`, `S = F_2[Q]`, `pi : S ->> R` the evaluation,
`K = ker pi`, `K^+ = F_2 1 + K`.

`Theta_2 : M_2(R) -> R`, `(a_ij) -> sum_(i,j) s_i a_ij t_j`, is a unital ring
isomorphism. `delta(q) = Theta_2(q I_2) = s_0 q t_0 + s_1 q t_1`, and `delta_*` is its
linear extension to `S`. The constants are `u = Theta_2([[1,1],[0,1]]) = 1 + s_0 t_1`,
`v = Theta_2([[1,0],[1,1]]) = 1 + s_1 t_0`, `g = uv = Theta_2(M_g)` with
`M_g = [[0,1],[1,1]]`, and `H = <u, v> = Theta_2(GL_2(F_2)) ~= S_3`. Put
`z = [1] + [g] + [g^2]`.

## Theorem

`mu : S -> S`, `mu(a) = delta_*(a) z`, is an injective ring homomorphism with
`mu(1) = z` and image in `zSz`, and `z` lies in `K`. Hence

1. `b a = 1 != a b` in `S` gives `B A = 1 != A B` for `A = (1 - z) + mu(a)`,
   `B = (1 - z) + mu(b)`, with `pi(A) = pi(B) = 1` and `A - 1, B - 1` in `K`;
2. `S` is directly finite iff `K^+` is iff `zSz` is, at every matrix size.

The map `A = Phi(a)` of `gk-l2-visible` is the same map, written `delta(x) z + (1 - z)`.

## Proof

**1. Scalars and constants.** A scalar matrix `q I_2` commutes with every matrix over
the central subfield `F_2`, so `delta(q)` commutes with `H`. If `delta(q) = Theta_2(M_h)`,
injectivity of `Theta_2` makes `M_h = q I_2` a scalar matrix of `GL_2(F_2)`, whose centre
is trivial, so `q = 1`. Thus `(q, h) -> delta(q) h` embeds `Q x H` in `Q`, and
`J : S (x)_(F_2) F_2[H] = F_2[Q x H] -> S` is an injective ring homomorphism.

**2. The evaluation-killed block.** `e_0 = 1 + g + g^2` is idempotent in `F_2[H]`
(`g^3 = 1`, characteristic two) and central (`<g>` is normal in `S_3`). `z = J(1 (x) e_0)`
and `pi(z) = Theta_2(I_2 + M_g + M_g^2) = 0`, since `M_g^2 = [[1,1],[1,0]] = M_g + I_2`.

**3. Injectivity of `mu` itself, not only of `J`.** `mu(a) = J(a (x) e_0)`. For `a != 0`
the tensor `a (x) e_0` is nonzero in `S (x)_(F_2) F_2[H]`, because the tensor product is
over a field and `e_0 != 0`. `J` is injective, so `mu(a) != 0`. Multiplicativity is
`J(a (x) e_0) J(b (x) e_0) = J(ab (x) e_0^2)`. Centrality of `e_0` in `F_2[H]`, together
with `delta_*(S)` commuting with `F_2[H]`, gives `mu(a) = z mu(a) z`.

This is the point `gk-kdf-structure` asked a verifier to check. No nonzero `a` has
`delta_*(a) z = 0`, so a strict pair stays strict: `mu(a) mu(b) = mu(ab) = z` would force
`ab = 1`.

**4. The pair.** `(1 - z) mu(x) = mu(x) (1 - z) = 0`, so
`B A = (1 - z) + mu(ba) = 1` and `A B = (1 - z) + mu(ab) != 1`. `pi(mu(x)) = pi(delta_*(x)) pi(z) = 0`
gives `pi(A) = pi(B) = 1`. `A - 1 = mu(a) - z` lies in the ideal `K`, which contains `z`.

**5. The equivalences.** `K^+` and the padded corner `(1 - z) + zSz` are unital subrings
of `S`, which gives the reverse implications. `M_n(mu)` with `z I_n` gives every `n`.

## Consequences

1. The dichotomy of `leavitt-inverse-defects-are-visible-or-invisible` collapses on the
   existence side: `S` fails direct finiteness iff (I*). (V*) implies (I*). Whether (I*)
   implies (V*) is not known.
2. `leavitt-evaluation-kernel-unitization-not-directly-finite` is equivalent to
   `leavitt-unit-group-algebra-not-directly-finite`, and its negation is equivalent to
   `leavitt-unit-group-algebra-is-directly-finite`. Every obstruction recorded against the
   invisible problem obstructs the whole Kaplansky question for `Q`.
3. Kaplansky for `Q` is equivalent to direct finiteness of the single corner `zSz`, which
   lies in `K`, and the linear case of Gottschalk's conjecture for `Q` is equivalent to it.
4. `mu` is the evaluation-invisible twin of `lambda(a) = delta_*(a) f` of
   `leavitt-primitive-corner-recursive-extension`. That map cuts the scalar copy of `S`
   inside the visible block `e = [g] + [g^2]`; `mu` cuts it by the complementary block
   `e_0`.

## General criterion: every field, every d, every level

**Setting.** `F` is a field, `d >= 2`, and `R` is a unital `F`-algebra with a Leavitt family
`s_1, ..., s_d, t_1, ..., t_d` (`t_i s_j = delta_ij`, `sum_i s_i t_i = 1`), for instance
`L_F(1,d)`. `Q = R^x`, `S = F[Q]`, `pi : S -> R` is the evaluation, `K = ker pi` and
`K^+ = F 1 + K`. For `k >= 1` put `n = d^k`. Words `gamma` of length `k` give `S[gamma]` and
`T[gamma]` with `T[gamma] S[gamma'] = delta_(gamma, gamma')` and
`sum_(|gamma| = k) S[gamma] T[gamma] = 1`. These are (M1) and (M2) of
`research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md`, whose proofs run
verbatim on `d` letters. So

    Theta_n : M_n(R) -> R,     (a_(gamma, gamma')) -> sum S[gamma] a_(gamma, gamma') T[gamma'],

is a unital ring isomorphism, with inverse `r -> (T[gamma] r S[gamma'])`. Put
`delta_n(q) = Theta_n(q I_n)`, and let `rho_n : F[H] -> M_n(F)` be the natural representation of
a subgroup `H <= GL_n(F)`.

**Theorem 6.** Let `H <= GL_n(F)` contain no scalar matrix except `I_n`, and let
`e = sum_h e_h h` be a nonzero idempotent of `F[H]` with `rho_n(e) = 0`. Put
`z = sum_h e_h [Theta_n(h)]` in `S` and `mu(a) = delta_(n*)(a) z`. Then `z` is an idempotent of
`K`, `mu : S -> zSz` is an injective ring homomorphism with `mu(1) = z`, and

    S directly finite  <=>  K^+ directly finite  <=>  zSz directly finite,

at every matrix size. Every pair `b a = 1 != a b` in `S` becomes the pair
`(1 - z) + mu(a)`, `(1 - z) + mu(b)` over `1`, with defect in `K`.

*Proof.*
1. `Theta_n` is injective and sends `GL_n(F)` into `Q`, and `delta_n : Q -> Q` is an injective
   homomorphism. `F` is central in `R`, so a scalar matrix `q I_n` commutes with `M_n(F)`, and
   `delta_n(Q)` commutes with `Theta_n(H)`. If `delta_n(q) = Theta_n(h)`, injectivity of
   `Theta_n` gives `h = q I_n`, a scalar matrix lying in `H`. So `h = I_n` and `q = 1`. Hence
   `(q, h) -> delta_n(q) Theta_n(h)` is an injective homomorphism `Q x H -> Q`. It sends distinct
   basis elements of `F[Q x H]` to distinct basis elements of `S`, so
   `J : S (x)_F F[H] = F[Q x H] -> S` is an injective ring homomorphism.
2. `z = J(1 (x) e)` is idempotent, and `pi(z) = sum_h e_h Theta_n(h) = Theta_n(rho_n(e)) = 0`,
   because `Theta_n` is `F`-linear.
3. `mu(a) = J(a (x) e)`. So `mu(a) mu(b) = J(ab (x) e^2) = mu(ab)`, `mu(1) = z`, and
   `z mu(a) = mu(a) = mu(a) z`, which puts `mu(S)` inside `zSz`. For `a != 0`, `a (x) e != 0`,
   because the tensor product is over a field and `e != 0`. `J` is injective, so `mu(a) != 0`.
   Centrality of `e` in `F[H]` is not needed.
4. The pair and the equivalences follow as in Steps 4 and 5 of the binary proof, using
   `pi(mu(a)) = pi(delta_(n*)(a)) pi(z) = 0`.

Two special cases:
* **Binary theorem:** `F = F_2`, `d = 2`, `k = 1`, `H = GL_2(F_2)`, `e = 1 + g + g^2`.
* **Whole ternary group algebra `F_3[L_(F_3)(1,2)^x]`:** `F = F_3`, `d = 2`, `k = 2`, with
  `gk-l3-kernel`'s Klein group (below). That lane's node
  `ternary-anti-central-failures-transfer-into-kernel-corners` cuts the same map by `eps_-`.

## Existence over every finite field

**Lemma 7.** Let `h` in `GL_n(F_q)` have order `m` prime to `q`, no eigenvalue `1`, and no scalar
power other than `I_n`. Then `H = <h>` and `e = m^(-1) sum_(i < m) h^i` satisfy the hypotheses
of Theorem 6.

*Proof.* `e` is the averaging idempotent of `H`, and `rho_n(e)` is the projection onto the fixed
space of `h`, which is `0`.

**Proposition 8.** For every prime power `q` and every `d >= 2` with `(q, d) != (3, 2)`, such an
`h` exists at level `k = 1`.

*Proof.*
* **`d = 2`, `q != 3`.** `q - 1` and `q + 1` differ by `2`, so they are both powers of two (or `1`)
  only when `q = 3`. Otherwise some odd prime `r` divides one of them, and `r` is prime to `q`.
  * If `r | q - 1`, take `lambda` in `F_q^x` of order `r` and `h = diag(lambda, lambda^(-1))`.
    `h^j` is scalar iff `lambda^(2j) = 1` iff `r | j`.
  * If `r | q + 1` and `r` does not divide `q - 1`, take `lambda` in `F_(q^2)^x` of order `r`, and
    let `h` be multiplication by `lambda` on `F_(q^2) ~= F_q^2`. `h^j` is scalar iff `lambda^j`
    lies in `F_q` iff `r | j(q - 1)` iff `r | j`.

  The eigenvalues are `lambda` and `lambda^(-1)`, or `lambda` and `lambda^q`, and none is `1`.
* **`d >= 3`, `(q, d) != (2, 6)`.** Zsigmondy's theorem: for coprime `a > b >= 1`, `a^n - b^n` has a
  primitive prime divisor except when `(a, b, n) = (2, 1, 6)`, or `n = 2` and `a + b` is a power
  of two. So `q^d - 1` has a prime divisor `r` dividing no `q^j - 1` with `j < d`. Such an `r` is
  odd (for odd `q`, `2 | q - 1`; for even `q`, `q^d - 1` is odd) and prime to `q`. Take `lambda`
  in `F_(q^d)^x` of order `r`. It lies in no proper subfield. Let `h` be multiplication by `lambda`
  on `F_(q^d) ~= F_q^d`; its eigenvalues are the `d` conjugates of `lambda`, none equal to `1`.
  `h^j` is scalar iff `lambda^j` lies in `F_q` iff `r | j(q - 1)` iff `r | j`.
* **`(q, d) = (2, 6)`.** `h = diag(g, g, g)`, with `g` in `GL_2(F_2)` of order `3`. It has no
  eigenvalue `1`, and `GL_6(F_2)` has no scalar except `I`.

### The case `(q, d) = (3, 2)`

Over `F_p` with `p` odd the constants contain the scalar matrices `lambda I_2`, whose images are
the central scalars `lambda = delta(lambda)` of the Leavitt algebra. So the hypothesis that `H`
be scalar-free has content.

**Proposition 9 (level one is empty over `F_3`).** No subgroup `H <= GL_2(F_3)` without `-I_2`
carries a nonzero idempotent `e` with `rho_2(e) = 0`.

*Proof.* `-I_2` is the only scalar other than `I_2`, and the only central involution.
* **Order-4 elements.** An element `h` of order 4 has `h^2 = -I_2`. If `h^2` had eigenvalues `1`
  and `-1`, `h` would have an eigenvalue `nu` with `nu^2 = -1`. Its Frobenius conjugate
  `nu^3 = -nu` would be the other eigenvalue, and it squares to `-1`, not `1`.
* **Commuting involutions.** Two commuting involutions other than `-I_2` are simultaneously
  diagonalizable, as `diag(1,-1)` and `diag(-1,1)`, and their product is `-I_2`.

So a scalar-free `H` has 2-part of order at most `2`, and `|H|` divides `6`, because
`|GL_2(F_3)| = 48`. The possible `H`:
* **`H = 1` or `H = <u>` with `u` unipotent.** `F_3[H]` is local, so its only idempotents are `0`
  and `1`.
* **`H = <s>`, `s` conjugate to `diag(1,-1)`.** The nontrivial idempotents `-(1 + s)` and
  `-(1 - s)` map to the two rank-one eigenprojections.
* **`|H| = 6`.** An element of order 6 would cube to an involution commuting with a unipotent `u`.
  The centralizer of `u = [[1,1],[0,1]]` is `{[[a,b],[0,a]]}`, and its only involution is `-I_2`.
  So `H ~= S_3 = <u, s>`. The simple `F_3[S_3]`-modules are the trivial and sign modules, and
  `V = F_3^2` has both as composition factors.

  A nonzero idempotent `e` with `eV = 0` would make `F_3[H] e` a nonzero projective with
  `Hom(F_3[H] e, V) = eV = 0`. So some projective cover `P_T` of a simple module `T` would have
  `Hom(P_T, V) = 0`. That is impossible: `dim Hom(P_T, V)` is the multiplicity of `T` in `V`,
  which is `1` for both simple modules.

In particular averaging idempotents of scalar-free subgroups fail, which `gk-l2-visible` also
reports.

**`p = 3`, level two works.** `gk-l3-kernel` landed the ternary transfer as
`ternary-anti-central-failures-transfer-into-kernel-corners` (commit ab42f3cff8). It uses the
level-two constants `Theta_4(GL_4(F_3))` and the scalar copy
`delta_4(g) = sum_(|gamma| = 2) S[gamma] g T[gamma]`. The Klein group generated by
`h_1 = diag(1,1,-1,-1)` and `h_2 = diag(-1,-1,1,-1)` does not contain `-I_4`. Its
averaging idempotent `E = [1] + [h_1] + [h_2] + [h_1 h_2]` (`4 = 1` in `F_3`) is killed by
the natural 4-dimensional representation, since `(1 + h_1)(1 + h_2) = 0`. So on the
anti-central summand the invisible half is universal over `F_3` as well. The obstruction
above is exactly why one must pass to level two.

A Singer element works at level two as well: `5` is a primitive prime divisor of
`3^4 - 1 = 80`, so an element of order `5` in `GL_4(F_3)` satisfies Lemma 7.

**Corollary 10.** For every prime power `q` and every `d >= 2`, let `R = L_(F_q)(1,d)` and
`S = F_q[R^x]`. Then `S` is directly finite iff `F_q 1 + ker pi` is directly finite iff one kernel
corner `zSz` is, at every matrix size. Every direct-finiteness failure of `S` has an
evaluation-invisible copy. Level one suffices except for `(q, d) = (3, 2)`, which needs level two.

**Scope.** Theorem 6 has no restriction on the field. Only existence at level one fails, and only
for `(q, d) = (3, 2)`. Nothing here decides direct finiteness for any `q`. The same criterion
applies to every unital algebra carrying a Leavitt family of type `(1,d)`, such as tensor hosts.
