# Numerical window relations never force balance over a nonamenable decoder

Lane `w4-window-boundary`, 2026-09-12. Supports `numeric-window-relations-do-not-force-balance`, which
invalidates `balance-from-numeric-window-relations`, and records an Attempts entry on
`every-injective-ca-preserves-uniform-bernoulli-measure`.

The open step isolated by `w3-bern-window` (`research/artifacts/window-balance-mass-transport-2026-09-12.md`)
is to remove the boundary factor `q^|d_N E|` from the decoder fiber bound on a cofinal family of windows.
This artifact shows that no argument using those relations only as numbers can do it, over any group,
once the decoder memory generates a nonamenable subgroup. When it generates an amenable subgroup, the
numbers already give a uniform site law. So the numerical form of relations (a), (b), (c) is exactly as
strong as amenability of the decoder memory group.

## 1. The numerical relations

`G` is a group, `A` a finite alphabet with `q = |A| >= 2`, and `mu` the uniform product measure on `A^G`.
For a finite window `E` and finite `N` containing `e`, `int_N E = {g : gN is contained in E}`, as in
the w3-bern-window artifact. Let `nu` be a probability measure on `A^G`, `M` and `N` finite sets containing
`e`, and write `nu[p]_E` for the measure of the cylinder of `p in A^E`. The relations are:

- **(R1)** `nu` is invariant under the left shift.
- **(R2)** Integral counts and finite dependence for the memory `M`:
  `c_E(p) = q^|EM| nu[p]_E` is a nonnegative integer for every finite `E` and `p`, and the restrictions
  of `nu` to `U` and `U'` are independent whenever `UM` and `U'M` are disjoint.
- **(R3)** Decoder decay with parameter `N`: `nu[p]_E <= q^(-|int_N E|)` for every finite `E` and
  every `p in A^E`.
- **(R4)** Some cylinder has `nu`-measure `0`.

If `tau` is an injective automaton with memory `M` and a left-inverse automaton with memory `N`, then
`nu = tau_* mu` satisfies R1 and R2 (the `c_E(p)` are its fiber counts, and outputs on `U` read inputs on
`UM`), R3 by `decoder-window-fiber-bound-loses-exactly-the-boundary`, and R4 exactly when `tau` is not
surjective. R1, R3, R4 are relations (a), (b), (c) of the w3-bern-window artifact, and R2 adds the
integrality and dependence range of the counts.

A *numerical argument* for balance at alphabet size `q` is a derivation, from R1–R4 alone, that the
one-site marginal of `nu` is uniform. Balance at any window containing a site implies the uniform site
law, so ruling out the site law rules out every window.

## 2. Amenable decoder memory: R3 alone gives a uniform site law

**Proposition 1.** If `N` generates an amenable subgroup `H`, every shift-invariant `nu` satisfying R3
has uniform one-site marginal.

*Proof.* Take right Følner sets `F_k` in `H`: `|F_k n \ F_k| / |F_k| -> 0` for each `n` in `N`. They
exist because amenability gives left Følner sets, and inversion turns those into right ones. If
`g in F_k \ int_N F_k`, some `gn` is outside `F_k`, so `g in F_k \ F_k n^-1`. The sets `F_k` and
`F_k n^-1` have equal size, so `|F_k \ F_k n^-1| = |F_k n^-1 \ F_k| = |F_k \ F_k n|`, and this also equals
`|F_k n \ F_k|`. Hence `|F_k \ int_N F_k| <= sum_n |F_k n \ F_k| = o(|F_k|)`.

Let `y` be the coordinate process under `nu`. By R3 every pattern on `F_k` has probability at most
`q^(-|int_N F_k|)`, so the Shannon entropy satisfies `H(y|F_k) >= |int_N F_k| log q`. Subadditivity and
invariance give `H(y|F_k) <= |F_k| H(y(e))`. Therefore
`H(y(e)) >= (|int_N F_k| / |F_k|) log q -> log q`, and a law on `q` symbols with entropy `log q` is
uniform. QED

`amenable-decoder-memory-forces-surjectivity` proves more in this case, namely surjectivity, from the
pointwise decoder identity. Proposition 1 shows that the counting shadow R3 already reaches the site law
here, so Section 3 is sharp.

## 3. Nonamenable decoder memory: R1–R4 hold for unbalanced measures

**Lemma 2.** If `N` (containing `e`) generates a nonamenable subgroup `H`, there is `theta_N < 1` with
`|int_N E| <= theta_N |E|` for every finite `E` in `G`.

*Proof.* First, there is `eps > 0` with `|FN| >= (1 + eps)|F|` for every finite nonempty `F` in `H`.
Otherwise, for every `eps` some `F` has `|FN \ F| < eps|F|`, because `F` is contained in `FN`. Then
`|Fn \ F| < eps|F|` and `|Fn^-1 \ F| = |F \ Fn| = |Fn \ F| < eps|F|` for each `n` in `N`. Along words,
`|Fw \ F| <= sum` over letters, so these `F` are right Følner sets for `H`, and `H` is amenable, a
contradiction.

For finite `F` in `G`, split `F` along the left cosets `gH`. Right multiplication by `N` preserves each
coset, and `g^-1 (F ∩ gH)` lies in `H`, so again `|FN| >= (1 + eps)|F|`. Put `I = int_N E`. Then `IN` is
contained in `E`, so `(1 + eps)|I| <= |E|`. Take `theta_N = 1/(1 + eps)`. QED

**Theorem 3 (merge measure, large alphabets).** Let `N` generate a nonamenable subgroup, `theta = theta_N`,
`M` any finite set containing `e`, and `q >= 3` with `q^(1 - theta) >= 2`. Pick distinct `a_1, a_2` in `A`,
let `f : A -> A` fix every symbol except `f(a_2) = a_1`, and let `nu` be the image of `mu` under
`phi(x)(g) = f(x(g))`. Then `nu` satisfies R1–R4 for `M` and `N`, and its one-site law is not uniform.

*Proof.* `nu` is the product of copies of `lambda = f_*(uniform)`, where `lambda(a_1) = 2/q`,
`lambda(a_2) = 0` and `lambda(a) = 1/q` otherwise.
- R1: a product measure is invariant.
- R2: `c_E(p) = q^(|EM| - |E|) * prod_(g in E) q lambda(p(g))`. That is `0` if `p` takes the value `a_2`,
  and `q^(|EM|-|E|) 2^#{g : p(g) = a_1}` otherwise, an integer. Independence holds for all disjoint sets.
- R4: the cylinder `{x(e) = a_2}` has measure `0`.
- R3: `nu[p]_E <= (2/q)^|E| = q^(-(1 - log_q 2)|E|) <= q^(-theta|E|) <= q^(-|int_N E|)`, using
  `q^(1-theta) >= 2` and Lemma 2.

The site law `lambda` is not uniform. QED

**Proposition 4 (binary alphabet, decoder memory containing a free ball).** Let `a, b` in `G` generate a
free subgroup `L` of rank 2, and let `c` in `G` have infinite order. Put `q = 2`, `M = {e, c}`, and let `N`
contain the ball `B_2` of radius 2 in `L` for the generators `a^{±1}, b^{±1}`. Let `nu` be the image of
`mu` under `phi(x)(g) = x(g) x(gc)`, the AND rule. Then `nu` satisfies R1–R4 and its site law is
`(3/4, 1/4)`.

*Proof.*
- **R1 and R2.** `phi` is an automaton with memory `M`.
- **R4.** Outputs `1` at `e` and at `c^2` force `x(c) = x(c^2) = x(c^3) = 1`, so the output at `c` is `1`.
  The pattern `(1, 0, 1)` on `(e, c, c^2)` therefore has measure `0`.
- **Decay.** Inputs on distinct cosets `g<c>` are independent. On one coset, identified with `Z`, a run of
  `l` consecutive sites reads `l + 1` inputs. The number of inputs giving outputs `p_1, ..., p_l` is
  `1^T T_(p_1) ... T_(p_l) 1`, with `1 = (1,1)^T` and transfer matrices indexed by consecutive input bits:
  `T_0 = [[1,1],[1,0]]` and `T_1 = [[0,0],[0,1]]`. `T_0` is symmetric with eigenvalues `phi_g` and
  `-1/phi_g`, where `phi_g` is the golden ratio, so its norm is `phi_g`; the norm of `T_1` is `1`. So the
  count is at most `|1|^2 phi_g^l = 2 phi_g^l`, and the probability is at most `(phi_g / 2)^l`.
  Distinct maximal runs in one coset read disjoint inputs, since a run ending at `t` reads up to `t + 1`
  and the next run starts at `t + 2` or later. So for every finite `E` and `p`,
  `nu[p]_E <= (phi_g/2)^|E| = 2^(-kappa |E|)` with `kappa = log_2(2/phi_g) = 0.3057...`.
- **Interiors.** The Cayley graph of `L` on `a^{±1}, b^{±1}` is the 4-regular tree. For finite `C` inside
  one left coset of `L`, a point of `int_(B_1) C` has degree 4 in the forest induced on `C`. A component
  with `n >= 2` vertices, `k` of them of degree 4, has `2(n - 1) >= 4k + (n - k)`, so `k <= (n - 2)/3`.
  Singleton components have `k = 0`. So `|int_(B_1) C| <= |C|/3`. Since `B_2 = B_1 B_1`,
  `int_(B_2) C = int_(B_1)(int_(B_1) C)`, and `|int_(B_2) C| <= |C|/9`. For finite `E` in `G`, split along
  left cosets of `L`, which right multiplication by `B_2` preserves, and use that `int_N E` is contained in
  `int_(B_2) E`: `|int_N E| <= |E|/9 <= kappa|E|`.
- **R3.** `nu[p]_E <= 2^(-kappa|E|) <= 2^(-|int_N E|)`. QED

**Corollary 5.** Numerical arguments do not prove a uniform site law, and so do not prove balance at any
window, in either of these cases:
- at every alphabet size `q >= 2^(1/(1 - theta_N))`, once the decoder memory generates a nonamenable
  subgroup (Theorem 3);
- at `q = 2`, once the decoder memory contains the radius-2 ball of a free pair (Proposition 4).

The goal quantifies over every alphabet size, so any numerical proof of it would in particular work at
the large sizes of Theorem 3. Whether numerical arguments can reach small alphabets for every nonamenable
decoder group is left open: Proposition 4 needs `theta_N <= 0.3057`.
