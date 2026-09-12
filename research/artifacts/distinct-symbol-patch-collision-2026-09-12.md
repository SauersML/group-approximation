# Distinct-symbol single patches reduce to linear strictness

Lane `w5-bal-distinct`, 2026-09-12.

**Target.** `ternary-three-address-injective-automata-have-balanced-rules`, at the case that
`single-patch-ternary-rules-linear-reduction-2026-09-12.md` (Section 2.2) left open: an affine
three-address ternary rule patched at one pattern whose three symbols are distinct.

**Result.**
- **Theorem 1.** Such a rule is not injective when its linear part is surjective, over every group and
  on every placement. No commutation hypothesis is needed. If the linear part is bijective, the rule is
  not even pre-injective.
- **Corollary 3.** With `single-patch-ternary-rules-reduce-to-linear-strictness` and the constant test,
  every ternary three-address rule that differs from an affine rule at exactly one pattern is injective
  over `G` only if its linear part is a linear strict automaton over `F_3` on `G`.

## 0. Setup

- **Alphabet, group, memory.** `A = F_3`, `G` any group, `M = {m_1, m_2, m_3}` three distinct elements
  of `G`. Indices are read mod 3. `tau_mu(x)(g) = mu(x(g m_1), x(g m_2), x(g m_3))`.
- **Affine part.** `lambda = c_1 x_1 + c_2 x_2 + c_3 x_3 + c_0`, linear automaton
  `L(d)(g) = sum_alpha c_alpha d(g m_alpha)`, and `S = c_1 + c_2 + c_3`.
  Then `tau_lambda(x + d) = tau_lambda(x) + L(d)`.
- **Patch.** `p = (p_1, p_2, p_3)` with three distinct symbols, `epsilon` in `{1, 2}`,
  `mu = lambda + epsilon [pattern = p]`. Write `P(y)(g) = 1` iff `(y(g m_alpha))_alpha = p`.
  So `tau_mu = tau_lambda + epsilon P`.
- **Collision criterion.** If `L(d) = -epsilon delta_h`, `x' = x + d`, `P(x') = delta_h` and
  `P(x) = 0`, then `tau_mu(x') = tau_lambda(x) - epsilon delta_h + epsilon delta_h = tau_mu(x)`.

## 1. The collision

**Theorem 1.** If `L` is surjective, `tau_mu` is not injective. If `L` is bijective, `tau_mu` is not
pre-injective.

*Proof.*

**Step 0 (preimage).** Take `d_0` with `L(d_0) = -epsilon delta_1`, and `d = d_0(h^-1 .)`. If `L` is
bijective, its inverse is a linear automaton and `d_0` has finite support. On `hM` the configurations
are forced: `x' = p` and `x = e`, where `e_beta = p_beta - d_0(m_beta)`.

**Step 1 (breaking at coordinate `i`).** Fix `i`.
- `phi_i(g) = g m_i` is a bijection of `G`, and `phi_i^-1(hM) = {h, g_(i+1), g_(i+2)}` with
  `g_beta = h m_beta m_i^-1`.
- At every site `w` outside `hM`, choose `x(w)` outside `{p_i, p_i - d(w)}`. Then neither `x` nor `x'`
  carries `p_i` at `w`. So a translate whose `i`-th site lies outside `hM` shows `p` in neither
  configuration.
- **At `h`.** `x'` shows `p`. `x` does not, because `L(d)(h) = -epsilon != 0` forces `d != 0` on `hM`.
- **At `g_beta`, `beta != i`.** Its `i`-th site is `h m_beta`, where `x'` carries `p_beta != p_i`, so
  `x'` does not show `p`. `x` can show `p` there only if `e_beta = p_i`.
- So the criterion holds at `i` unless some `beta != i` has `e_beta = p_i` (**danger at `i`**).

**Step 2 (danger at every index).** This is the case of the reference artifact, Section 2.2.
- **Shape of `e`.** Every symbol `p_i` is some `e_beta` with `beta != i`. So `e` is a bijection onto
  `F_3`, and `pi = p^-1 o e` is a derangement of three points, hence a 3-cycle. Then `p o pi o p^-1`
  is a 3-cycle of `F_3`, hence a translation. So `d_0 = kappa` on `M` for some `kappa != 0`, and
  `e_beta = p_beta - kappa`.
- **Consequences.** `L(d_0)(1) = kappa S = -epsilon`, so `S != 0`. For each `i`, exactly one
  `beta != i` has `e_beta = p_i`, namely `beta = p^-1(p_i + kappa)`. This is a 3-cycle on indices.
- **Orientation.** Swapping two addresses permutes `M` and `c` and changes nothing else. So assume the
  3-cycle is `i -> i + 1`. Equivalently `p_(i+1) = p_i + kappa` for every `i`, and `e_beta = p_(beta-1)`.

**Step 3 (the danger translate at `i`).** Fix `i`.
- **Which translate.** `t = g_(i+1) = h m_(i+1) m_i^-1` is in danger. The other one, `g_(i+2)`, is safe,
  since `e_(i+2) = p_(i+1) != p_i`.
- **Its other sites.** For `j` in `{i+1, i+2}`, position `j` of `t` is `w_j = h u_j` with
  `u_(i+1) = m_(i+1) m_i^-1 m_(i+1)` and `u_(i+2) = m_(i+1) m_i^-1 m_(i+2)`. It is enough that
  `x(w_j) != p_j` for one `j`.
- **If `w_j` is in `hM`, say `w_j = h m_gamma`.** Then `x(w_j) = e_gamma = p_(gamma-1)`, which differs
  from `p_j` unless `gamma = j + 1`.
- **If `w_j` is not in `hM`.** It is the `i`-th site of exactly one translate other than `h, t, g_(i+2)`,
  and Step 1 forbids `{p_i, p_i - d(w_j)}` there. Forbid `p_j` as well. A symbol remains unless
  `p_i - d(w_j)` is the third symbol `p_k`, `k` not in `{i, j}`. With `p_(i+1) = p_i + kappa` and
  `p_(i+2) = p_i - kappa`, that exception is `d_0(u_(i+1)) = kappa` for `j = i+1`, and
  `d_0(u_(i+2)) = -kappa` for `j = i+2`.
- **Call `i` stuck** if both `j` fail. Then:
  - `j = i+1` fails only if `u_(i+1) = m_(i+2)`, or `u_(i+1)` is not in `M` and `d_0(u_(i+1)) = kappa`.
    Either way `d_0(u_(i+1)) = kappa`.
  - `j = i+2` fails only if `u_(i+2) = m_i`, so `d_0(u_(i+2)) = kappa`, or `u_(i+2)` is not in `M` and
    `d_0(u_(i+2)) = -kappa`.
- **The linear equation at `g_0 = m_(i+1) m_i^-1`.** `g_0 != 1`, and `g_0 M` has `m_(i+1)`, `u_(i+1)`,
  `u_(i+2)` at positions `i, i+1, i+2`. So `L(d_0)(g_0) = 0` reads
  `c_i kappa + c_(i+1) d_0(u_(i+1)) + c_(i+2) d_0(u_(i+2)) = 0`.
  - If `i` is stuck with `d_0(u_(i+2)) = kappa`, this says `kappa S = 0`. Contradiction.
  - So a stuck `i` has `d_0(u_(i+2)) = -kappa`, and `c_i + c_(i+1) - c_(i+2) = 0`, that is
    `S - 2 c_(i+2) = 0`, that is `c_(i+2) = -S` (since `-2 = 1` in `F_3`).

**Step 4 (some index is not stuck).** If all three indices were stuck, then `c_1 = c_2 = c_3 = -S`, so
`S = -3S = 0`. Contradiction. At an index `i` that is not stuck, fill `x` as in Step 1 and, if needed,
change `x` at one free `w_j` as in Step 3. Now `P(x) = 0` and `P(x') = delta_h`, so `x` and `x'` collide.
If `L` is bijective they differ only on the finite set `supp d`. QED

*Checks.*
- **Sites in Step 3.** A free `w_j` is not the `i`-th site of `h`, `t` or `g_(i+2)`, since those lie in
  `hM`. So changing `x(w_j)` keeps its own translate broken.
- **No commutation.** Unlike Theorem 1.1 of the reference artifact, no relation among the `m_alpha` is
  used. The relations `u_(i+1) = m_(i+2)` and `u_(i+2) = m_i` are absorbed into the linear equation.
- **Sanity instance.** `G = Z`, `M = {0, 1, 2}`, `c = (1, 1, 2)`, `kappa = 1`, `p = (0, 1, 2)`. The
  preimage has `d_0 = 1` on `M` and `d_0(3) = 2`. Index 1 is stuck (`u_2 = 2 = m_3`, and `d_0(3) = -1`),
  and `c_3 = 2 = -S`. Index 2 is not stuck (`d_0(3) = 2 != kappa`).

## 2. Corollaries

**Corollary 2 (reduction to linear strictness).** If `tau_mu` is injective over `G`, then `L` is
injective and not surjective. That is, `x -> sum_alpha c_alpha x(g m_alpha)` is a linear strict
automaton over `F_3` on `G`.

*Proof.* Every pattern avoiding the symbol `p_1` is unpatched, so
`avoidable-patches-of-affine-rules-inherit-linear-injectivity` makes `L` injective. Theorem 1 makes it
non-surjective. QED

**Corollary 3 (every single patch).** Let `mu` differ from an affine rule `lambda` at exactly one pattern.
If `tau_mu` is injective over `G`, its linear part is a linear strict automaton over `F_3` on `G`.

*Proof.* By the pattern type.
- **Three distinct symbols:** Corollary 2.
- **Exactly two equal symbols:** `single-patch-ternary-rules-reduce-to-linear-strictness`, Corollary 1.2.
- **Constant pattern `(c, c, c)`:** constant configurations collide. The diagonal of `lambda` is
  `c' -> S c' + c_0`, a bijection or constant, and changing its value at `c` leaves a non-bijection.
QED

**For the census claim.** Single-patch rules give no counterexample beyond linear strict automata over
`F_3`. What remains of `ternary-three-address-injective-automata-have-balanced-rules` is rules at
distance at least 2 from every affine rule (Section 3).

**Relation to Theorem 13'** (`constant-background-kills-unit-linear-defect-rules`). Its absorbed-translate
residue and the danger case of the reference artifact were two residues of the same unit case. For
single patches both are now empty.
