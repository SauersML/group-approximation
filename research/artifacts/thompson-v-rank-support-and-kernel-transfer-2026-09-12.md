# Rank models and the kernel for the Thompson V linear targets

Lane `w3-v-linear`, 2026-09-12. Supports `full-averaging-idempotent-kills-its-element-in-rank-models`
and `thompson-v-linear-witness-supports-kill-g-in-rank-models`. Section 3 (kernel transfer) lands
separately. Targets: `thompson-v-ternary-swap-idempotent-is-full` and
`thompson-v-order-three-averaging-idempotent-is-full`.

## 1. Full averaging idempotents die in rank models

**Setup.** `F` is a field of characteristic `p`, `H` a group, and `g` in `H` has finite order `m`
with `p` not dividing `m`. Put `e_g = m^-1 (1 + g + ... + g^(m-1))` in `F[H]`. Then
`e_g^2 = e_g` and `g e_g = e_g = e_g g`.

A *rank target* is an `F`-algebra `M` with a Sylvester rank function `rk`, meaning
`rk(1) = 1`, `rk(xy) <= min(rk x, rk y)` and `rk(e) + rk(1-e) = 1` for idempotents `e`, that is
faithful on idempotents: `rk(e) = 0` implies `e = 0`. Examples:
- `M_n(k)` with normalized rank, for a field `k` containing `F`;
- a rank ultraproduct `prod_omega M_(n_i)(k) / (rank-null)` over a field `k` of characteristic `p`,
  where the rank function is faithful on every element.

**Lemma 1.1.** If `c e_g b = 1` in `F[H]` for some `b, c`, then `sigma(g) = 1` for every group
homomorphism `sigma : H -> M^x` into a rank target `M`.

*Proof.*
- `sigma` extends to a unital algebra map `F[H] -> M`.
- `1 = rk(1) = rk(sigma(c) sigma(e_g) sigma(b)) <= rk(sigma(e_g))`.
- `sigma(e_g)` is idempotent, so `rk(1 - sigma(e_g)) = 1 - rk(sigma(e_g)) = 0`, and
  faithfulness gives `sigma(e_g) = 1`.
- `sigma(g) = sigma(g) sigma(e_g) = sigma(g e_g) = sigma(e_g) = 1`. QED

**Remarks.**
- The matrix form `C (e_g I_n) B = I_n` in `M_n(F[H])` gives the same conclusion, using the rank
  on `M_n(M)` normalized by `n`.
- This is stronger than direct-finiteness failure. Fullness of `e_g` forces `g` into the kernel of
  every rank model of every subgroup containing `g` and the supports of `b, c`.

## 2. Supports of witnesses for the V targets

The two targets (artifact `thompson-v-linear-counterexample-targets-2026-09-12.md`):
- ternary: `g = w`, codes `(0, 1) -> (1, 0)`, `p = 3`, `e_g = 2(1 + w)`;
- binary: `g = h`, codes `(00, 01, 1) -> (01, 1, 00)`, `p = 2`, `e_g = 1 + h + h^2`.

**Corollary 2.1.** Let `b, c` witness one of the targets, and let `H = <g, supp b, supp c> <= V`.
Then `g` lies in the kernel of every homomorphism from `H` into a rank target of characteristic
`p`. In particular:
1. `g` lies in the finite residual of `H`. A finite quotient `Q` gives the regular permutation
   representation `Q -> GL_|Q|(F_p)`, a rank target.
2. Every representation `H -> GL_n(k)` with `char k = p` kills `g`.
3. `H` is not residually finite, not LEF, not sofic and not `F_p`-linear sofic. Sofic and LEF
   approximations give ultraproducts of permutation matrices. By
   `monomial-rank-models-are-hamming-models` their rank distance from `1` is at least half the
   Hamming distance, so each is a rank target injective on `H`. A linear sofic approximation is
   one by definition.

*Proof.* `b, c` and `e_g` lie in `F_p[H]`, so `c e_g b = 1` holds there. Apply Lemma 1.1 to `H`.
Items 1–3 exhibit rank targets that keep `g` alive. QED

**Consequences for a search.**
- No witness is supported, together with `g`, in a finite, locally finite, residually finite,
  amenable or linear subgroup of `V`. That excludes the dyadic prefix-permutation groups, free
  subgroups, and every finitely generated subgroup of `V` with a faithful finite-dimensional
  representation.
- Both `w` and `h` preserve the cyclic order of prefixes, so they lie in Thompson's `T`. `T` is
  infinite and simple (Cannon–Floyd–Parry), hence equal to its finite residual, and `T`-internal
  witnesses pass the filter. The smallest known candidate hosts are non-residually-finite
  subgroups such as `T`, `V` and the Higman–Thompson groups.
- It is the `V`-internal form of `anti-central-rank-models-kill-ternary-corner-witnesses`, which
  needs `z`, `w` and `d` inside the ternary Leavitt unit group. No central element is needed here.

**Where it stops.** `V` has finite residual `V`, and no rank model of `V` is known. So the filter
does not decide either target. It locates a construction exactly in a subgroup where `g` survives
in no rank model.

## 3. Failures transfer into the kernel of the Leavitt evaluation

Supports `thompson-v-direct-finiteness-failures-transfer-into-kernel`. Let `p` be `2` or `3`,
`S = F_p[V]`, `pi : S -> L_(F_p)(1,2)` the linear extension of the cylinder embedding
`g -> sum_i S[b_i] T[a_i]`, and `K = ker pi`.

**Kernel idempotent.**
- `p = 3`: `x` swaps the depth-2 prefixes `00, 01` and fixes every other point; `y` swaps
  `10, 11`. Put `q = (1-x)(1-y)`.
- `p = 2`: `x` cycles three of the depth-3 prefixes inside `[0]`, for example
  `000 -> 001 -> 010 -> 000`, and fixes every other point; `y` is the same inside `[1]`. Put
  `q = (x+x^2)(y+y^2)`.

**Lemma 3.1.** `q` is a nonzero idempotent of `S` and `pi(q) = 0`.

*Proof.*
- `p = 3`: `x^2 = 1` gives `(2(1-x))^2 = 4(2 - 2x) = 2(1-x)`, and likewise for `y`. `x` and `y`
  commute (disjoint supports), so `q = 4(1-x)(1-y) = (2(1-x))(2(1-y))` is idempotent.
- `p = 2`: `x^3 = 1` gives `(x+x^2)^2 = x^2 + 2x^3 + x^4 = x + x^2`, and likewise for `y`.
- `q` is a combination of four distinct group elements, so `q != 0`.
- On the module `M` of Section 3 of the targets artifact, `pi(1-x)` vanishes on functions supported
  on `[1]`, since `x` acts there as `1`. Its range is supported on `[0]`. `pi(1-y)` has range
  supported on `[1]`, where `pi(1-x)` vanishes. So `pi(q) = pi(1-x) pi(1-y) = 0`, and `M` is
  faithful for `L_(F_p)(1,2)` (the algebra is simple). The case `p = 2` is the same with
  `x + x^2`, which acts as `1 + 1 = 0` off `[0]`. QED

**Tail-diagonal embedding.** Put `k = 2` for `p = 3` and `k = 3` for `p = 2`. For `g` in `V`
with codes `a_i -> b_i`, let `delta(g)` have codes `u a_i -> u b_i` for all words `|u| = k`. So
`delta(g) = sum_(|u|=k) S[u] g T[u]`.

**Lemma 3.2.** `delta : V -> V` is an injective homomorphism. Every `delta(g)` commutes with `x`
and `y`, and `delta(V) ∩ <x, y> = {1}`.

*Proof.*
- `delta(g)(u eta) = u g(eta)`, which is multiplicative and injective.
- `x` and `y` permute depth-`k` prefixes without touching tails: `x(u eta) = x(u) eta`. So
  `delta(g) x (u eta) = x(u) g(eta) = x delta(g) (u eta)`.
- `delta(g)` fixes every depth-`k` prefix, and a nontrivial element of `<x, y>` moves one. QED

**Theorem 3.3.** `mu(a) = delta_*(a) q` is an injective unital ring homomorphism `S -> qSq` with
`pi o mu = 0`. A pair `c a = 1 != a c` in `S` gives the pair `A = (1-q) + mu(a)`,
`C = (1-q) + mu(c)` in `1 + K` with `C A = 1 != A C`. So `S`, `F_p 1 + K` and `qSq` are directly
finite together. The same holds entrywise at every matrix size.

*Proof.*
- `q` commutes with `delta_*(S)` by Lemma 3.2, so `mu(ab) = delta_*(a) delta_*(b) q =
  mu(a) mu(b)`, and `mu(1) = q`.
- Injective: the elements `delta(g) xi`, `g` in `V` and `xi` in `supp q`, are pairwise distinct by
  Lemma 3.2, so `mu(a)` has coefficient `a_g q_xi` at `delta(g) xi`.
- `pi(mu(a)) = pi(delta_*(a)) pi(q) = 0`.
- `(1-q) mu(a) = 0 = mu(a)(1-q)`, so `C A = (1-q) + mu(c a) = (1-q) + q = 1`. Also
  `A C = (1-q) + mu(a c)`, which differs from `1` because `mu` is injective and `a c != 1`.
- `pi(A) = pi(1-q) = 1`, so `A, C` lie in `1 + K`. The converse is inclusion of unital subrings.
  QED

**For the targets.** A witness `c e_g b = 1` gives `mu(c) mu(e_g) mu(b) = q`. So its invisible
copy is a corner equation for the averaging idempotent of `delta(g)` inside `qSq`, which the
Leavitt evaluation cannot see.

**Where it stops.** It is a reformulation. No strict pair in `F_p 1 + K` is known.
