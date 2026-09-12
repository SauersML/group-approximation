# Independent derivation: every Kaplansky pair over the Leavitt unit group becomes an invisible pair

Lane `gk-l2-invisible`, 2026-09-12. This is an independent re-derivation of the theorem
that `gk-l2-visible` lands as the canonical claims
`leavitt-unit-group-algebra-embeds-in-kernel-corner` and
`leavitt-kaplansky-failures-have-invisible-witnesses`, with artifact
`research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md`. Both lanes found the
same construction within minutes of each other; the canonical ids are theirs. This
artifact supports the route `kernel-unitization-df-from-unit-group-algebra-df` and the
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

## Odd characteristic: where the argument stops

Over `F_p` with `p` odd, the constants `Theta_2(GL_2(F_p))` contain the scalar matrices
`lambda I_2`. Their images are the central scalars `lambda` of `L_(F_p)(1,2)`, and
`delta(lambda) = lambda`, so they meet `delta(Q)`. A transfer over `F_p` therefore needs a
subgroup `H' <= GL_2(F_p)` with `H'` meeting the scalars trivially, and an idempotent of
`F_p[H']` that the natural representation kills.

**`p = 3`, level one fails.** A `3'`-subgroup `H'` of `GL_2(F_3)` without nonzero fixed
vectors would let the averaging idempotent of `H'` be killed by `rho_2`. The
`3'`-subgroups are the 2-groups inside the Sylow `SD_16`. Every nontrivial 2-subgroup
acting without fixed vectors contains an element of order two without eigenvalue 1, and in
`GL_2(F_3)` the only such involution is `-I_2`, a scalar. So averaging idempotents of
scalar-free `3'`-subgroups of the level-one constants are never killed by `rho_2`.
`gk-l2-visible` reports the same obstruction.

**`p = 3`, level two works.** `gk-l3-kernel` landed the ternary transfer as
`ternary-anti-central-failures-transfer-into-kernel-corners` (commit ab42f3cff8). It uses the
level-two constants `Theta_4(GL_4(F_3))` and the scalar copy
`delta_4(g) = sum_(|gamma| = 2) S[gamma] g T[gamma]`. The Klein group generated by
`h_1 = diag(1,1,-1,-1)` and `h_2 = diag(-1,-1,1,-1)` does not contain `-I_4`. Its
averaging idempotent `E = [1] + [h_1] + [h_2] + [h_1 h_2]` (`4 = 1` in `F_3`) is killed by
the natural 4-dimensional representation, since `(1 + h_1)(1 + h_2) = 0`. So on the
anti-central summand the invisible half is universal over `F_3` as well. The obstruction
above is exactly why one must pass to level two.

For d-ary hosts the criterion is the same: constants `GL_(d^k)(F_q)` at some level `k`.
