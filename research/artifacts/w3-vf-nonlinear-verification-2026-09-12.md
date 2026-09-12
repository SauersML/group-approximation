# Wave-3 nonlinear-side verification (lane w3-vf-nonlinear)

Lane `w3-vf-nonlinear`, 2026-09-12. Independent re-derivations of landings from `w3-v-linear`,
`w3-measurable`, `w3-lattice`, `w3-nonformal`, `w3-stable-simple` and `w3-free-neg`. Each section
states the claims checked, the verdict, and any scope correction. A verdict line citing this
artifact is added to each proof route checked.

## 1. Thompson V rank support and kernel transfer (w3-v-linear, e66fba49c6 and d64ea6c143)

Artifact: `research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md`.

### 1.1 `full-averaging-idempotent-kills-its-element-in-rank-models`. Verdict: PASS.

- `sigma : H -> M^x` extends to a unital algebra map `F[H] -> M`, so
  `sigma(c) sigma(e_g) sigma(b) = 1` and `1 = rk(1) <= rk(sigma(e_g))`.
- A Sylvester rank function satisfies `rk(e) + rk(1-e) = rk(1)` for idempotents, because
  `diag(e, 1-e)` is equivalent to `diag(1, 0)` by invertible matrices and the rank of a block
  diagonal is the sum. So `rk(1 - sigma(e_g)) = 0`.
- Faithfulness on idempotents holds in both examples: normalized rank on `M_n(k)` is faithful on
  every element, and so is the induced rank on a rank ultraproduct, since the rank-null ideal has
  been quotiented out.
- `g e_g = e_g`, so `sigma(g) = sigma(g) sigma(e_g) = sigma(e_g) = 1`.
- Matrix form: the normalized rank on `M_n(M)` gives `rk(sigma(e_g)) = 1` in the same way.

### 1.2 `thompson-v-linear-witness-supports-kill-g-in-rank-models`. Verdict: PASS, with one scope sharpening.

- Target forms checked against main: both targets are scalar equations `c e b = 1` in `F_p[V]`.
  For `w` of order 2 over `F_3`, `2^-1 = 2` gives `e_w = 2(1+w)`. For `h` of order 3 over `F_2`,
  `3^-1 = 1` gives `e_h = 1 + h + h^2`. In both cases `p` does not divide the order.
- `b, c, e_g` lie in `F_p[H]`, so the equation holds in `F_p[H]` and Lemma 1.1 applies to `H`.
- Rank targets that would keep `g` alive:
  - A finite quotient `Q` gives the regular representation over `F_p`, faithful on `Q`. So `g` is
    in every finite-index normal subgroup, i.e. in the finite residual.
  - A sofic (or LEF) approximation into `Sym(n_i)` gives permutation matrices. For a permutation
    `P`, `rk(P - 1) = n - #cycles >= (moved points)/2`, and `rk(P - Q) <= #{i : P e_i != Q e_i}`.
    So the ultraproduct over `F_p` is a homomorphism with `rk(sigma(g) - 1) >= 1/2` for `g != 1`.
    This is `monomial-rank-models-are-hamming-models` with trivial scalars.
  - A linear sofic approximation separates elements by a positive constant, so its ultraproduct is
    injective.
- The exclusions (finite, locally finite, residually finite, amenable, linear supports) are
  correct: `H` is finitely generated, so locally finite means finite; amenable implies sofic; and
  finitely generated linear groups over any field are residually finite (Malcev).
- `w` is the rotation by `1/2` and `h` sends `[0,1/4), [1/4,1/2), [1/2,1)` onto
  `[1/4,1/2), [1/2,1), [0,1/4)` affinely. Both preserve the cyclic order, so both lie in `T`.
- **Scope sharpening.** The sentence "T-internal witnesses pass the filter" overstates. The filter
  is a statement about `H = <g, supp b, supp c>`, and `H <= T` need not be `T`. A witness supported
  in `T` whose `H` is residually finite is excluded. What is true: `T` itself equals its finite
  residual and has no nontrivial finite-dimensional representations (Malcev plus simplicity), while
  its soficity and linear soficity are open. So witnesses with `H = T`, or with `H` any subgroup
  where `g` survives in no known rank model, are not excluded by anything known. Sent to the author
  to reword.

### 1.3 `thompson-v-direct-finiteness-failures-transfer-into-kernel`. Verdict: PASS.

- `p = 3`: `x = (00 01)`, `y = (10 11)` have disjoint supports and order 2, and
  `(2(1-x))^2 = 8(1-x) = 2(1-x)` over `F_3`. So `q = (1-x)(1-y) = (2(1-x))(2(1-y))` is idempotent,
  with four distinct group elements in its support.
- `p = 2`: `x, y` are 3-cycles on depth-3 prefixes in `[0]`, `[1]`, and `(x+x^2)^2 = x + x^2`.
- `pi(q) = 0`, checked directly in `L_(F_p)(1,2)` without the sequence module:
  - `p = 3`: `pi(1-x) = (S00 - S01)(T00 - T01)` and `pi(1-y) = (S10 - S11)(T10 - T11)`. The middle
    factor `(T00 - T01)(S10 - S11)` vanishes, since `T_a S_b = 0` for incomparable `a, b`.
  - `p = 2`: `pi(x + x^2) = sum_(j != i) S_i T_j` over the three moved prefixes in `[0]`, and
    likewise in `[1]`. Every cross product contains some `T_(0..) S_(1..) = 0`.
  - The artifact's module argument (a nonzero module over the simple algebra is faithful) is also
    correct.
- `delta(g)(u eta) = u g(eta)` for `|u| = k` is an injective homomorphism into `V`. `x, y` act
  only on the depth-`k` prefix, so they commute with every `delta(g)`. `delta(g)` fixes every
  depth-`k` prefix, and nontrivial elements of `<x, y>` move one, so `delta(V) ∩ <x, y> = 1`.
- `mu(a) = delta_*(a) q` is multiplicative because `q` commutes with `delta_*(S)`, unital onto `q`,
  and injective: `delta(g) xi = delta(g') xi'` forces `g = g'` and `xi = xi'`, so the coefficient
  of `delta(g) xi` in `mu(a)` is `a_g q_xi`.
- Padding: `(1-q) mu(a) = 0 = mu(a)(1-q)`, so `CA = (1-q) + mu(ca) = 1`, and `AC = 1` would give
  `mu(ac) = mu(1)` and `ac = 1`. `pi(A) = 1`, so `A, C` lie in `F_p 1 + K`.
- Matrix sizes: apply `mu` entrywise. Diagonal entries of `(1-q) I + mu(a)` lie in `1 + K`, and
  off-diagonal entries lie in `K`.

**Decision status.** Nothing decision-level. `thompson-v-ternary-swap-idempotent-is-full` and
`thompson-v-order-three-averaging-idempotent-is-full` stay OPEN.
