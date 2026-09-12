# Single-patch ternary rules reduce to linear strictness

Lane `w4-bal-rigid`, 2026-09-12.

**Target.** `ternary-three-address-injective-automata-have-balanced-rules`, at the rigid rule `R` of
`small-memory-balance-census-2026-09-12.md` (Remark 3.4 and Section 5.2).

**Result.** `R`, and every affine three-address ternary rule patched at one pattern with a repeated
symbol, is injective over a group only if its linear part is already a linear strict automaton
there. When the linear part is a unit, the rule is not even pre-injective. So such rules give no
counterexample beyond linear ones.

## 0. Setup

- **Alphabet, group and memory.** `A = F_3`, `G` is a group, and `M = {1, a, b}` with `1, a, b`
  distinct. The automaton of a rule `mu` is `tau_mu(x)(g) = mu(x(g), x(ga), x(gb))`.
- **Affine part.** `lambda(x, y, z) = c_1 x + c_2 y + c_3 z + c_0`, with linear part `lambda_0` and
  linear automaton `L = tau_(lambda_0)`. So `L(d)(g) = c_1 d(g) + c_2 d(ga) + c_3 d(gb)` and
  `tau_lambda(x + d) = tau_lambda(x) + L(d)`.
- **Single patch.**
  - The pattern is `p = (s_0, s, s)` with `s_0 != s`, the patch value is `epsilon` in `{1, 2}`, and
    `mu = lambda + epsilon [pattern = p]`.
  - Write `P(y)(g) = 1` if `(y(g), y(ga), y(gb)) = p`, and `0` otherwise. Then
    `tau_mu = tau_lambda + epsilon P`.
- **Normalization.** Take any affine three-address rule patched at one pattern that repeats a
  symbol.
  - Permute addresses so the lone symbol reads the address `m`.
  - Replace the placement `M` by `m^-1 M`. This composes `tau` with a right translation, so it
    changes neither injectivity nor pre-injectivity.
  - The result has the form above.
- **The census rule.** `R` is the case `c = (1, -1, 1)`, `c_0 = 0`, `p = (0, 2, 2)`, `epsilon = 1`.

## 1. The collision

**Theorem 1.1.** Suppose `a` and `b` do not commute.
- If `L` is surjective, `tau_mu` is not injective.
- If `L` is bijective, `tau_mu` is not pre-injective.

*Proof.*

- **Choose `d`.** Fix `h` in `G`. Surjectivity gives `d` with `L(d) = -epsilon delta_h`, and `d != 0`.
  If `L` is bijective its inverse is a linear automaton, so `d` has finite support.
- **Special sites.**
  - `h`, `ha` and `hb` are distinct.
  - Call `(a^-1 b)^2 = 1` the involution case, and there put `g* = h b a^-1`.
  - `g*` is not `h` (that would give `a = b`), not `ha` (that would give `b = a^2`, which commutes
    with `a`), and not `hb` (that would give `a = 1`).
- **Choose `x`.** Each step forbids at most two of the three symbols, so a choice exists.
  1. `x(h) = s_0 - d(h)`, `x(ha) = s - d(ha)` and `x(hb) = s - d(hb)`. So `x' := x + d` equals `p`
     on `hM`.
  2. In the involution case, `x(g*)` lies outside `{s_0, s_0 - d(g*)}`.
  3. At every other site `w`, `x(w)` lies outside `{s, s - d(w)}`.
- **`s`-sites.** Let `Sigma(y) = {w : y(w) = s}`. Then `Sigma(x')` is contained in `{ha, hb, g*}`,
  and `Sigma(x)` in `{h, ha, hb, g*}`. Here `x'(h) = s_0 != s`, and step 3 keeps `s` out of both
  configurations at every other site.
- **Site lemma.**
  - **The criterion.** An occurrence of `p` in `y` at `g` needs `ga` and `gb` to be distinct points
    of `Sigma(y)`. For distinct sites `u, v`, the equations `ga = u`, `gb = v` have a solution iff
    `a^-1 b = u^-1 v`, and then `g = u a^-1`.
  - **Notation.** In the involution case write `t = b a^-1`, so that `b = ta` and `t^2 = 1`.
  - **The twelve ordered pairs of distinct sites from `{h, ha, hb, g*}`:**
    - `(ha, hb)` holds, with `g = h`.
    - `(hb, ha)` holds iff `(a^-1 b)^2 = 1`, and then `g = g*`.
    - `(h, ha)` gives `b = a^2`. `(hb, h)` gives `a = b^2`. `(h, g*)` and `(g*, h)` give `ta = at`.
      `(g*, hb)` gives `t = a^2`, so `b = a^3`. Each of these makes `a` and `b` commute.
    - `(ha, h)`, `(h, hb)`, `(hb, g*)`, `(ha, g*)` and `(g*, ha)` force `a = 1` or `b = 1`, which is
      impossible.
- **Occurrences.**
  - `x'` at `h`: yes, by step 1.
  - `x'` at `g*`: no, because `x'(g*) != s_0` by step 2.
  - `x` at `h`: this needs `d(h) = d(ha) = d(hb) = 0`, but then `L(d)(h) = 0`, whereas
    `L(d)(h) = -epsilon != 0`.
  - `x` at `g*`: no, because `x(g*) != s_0`.
  - Any other occurrence in either configuration uses a pair from the last two lines of the site
    lemma, and none of those holds.
  - So `P(x) = 0` and `P(x') = delta_h`.
- **Collision.** `tau_mu(x') = tau_lambda(x) + L(d) + epsilon delta_h = tau_lambda(x) = tau_mu(x)`,
  and `x' != x`.

QED

**Corollary 1.2 (reduction to linear strictness).** Let `mu` be a single-patch rule as in Section 0.
If `tau_mu` is injective over `G`, then `L` is injective and not surjective over `G`. That is, `L` is
a linear strict automaton over `F_3` on `G`.

*Proof.*
- **Restrict.** Let `H = <a, b>`. Configurations split over the cosets of `H`, so `tau_mu` is
  injective over `H`.
- **Case `lambda_0 = 0`.** Then `L` is not injective, and
  `avoidable-patches-of-affine-rules-inherit-linear-injectivity` gives a collision, using the
  symbol `s`, which occurs in `p`. So `lambda_0 != 0`. Then `lambda` is balanced, and the single
  patch makes `mu` unbalanced, with preimage counts `10, 9, 8`.
- **Case `H` abelian.** `H` is amenable, so an injective automaton over `H` is surjective
  (Gromov–Weiss) and has a balanced rule. That is a contradiction.
- **Case `H` not abelian.** The avoidable-patch proposition makes `L` injective over `H`, and
  Theorem 1.1 makes it non-surjective. Over `G`, `L` is a product of copies over the cosets, so it is
  injective and not surjective there too.

QED

**Consequences for `R`.**
- **Linear strictness.** If `tau_R` is injective over `G`, then `x -> x(g) - x(ga) + x(gb)` is a
  linear strict automaton over `G`. So `R` is not a new kind of counterexample: on every group where
  ternary linear automata are surjunctive, `R` is never injective.
- **The unit case.** The census's open case, where `1 - a + b` is a unit of `F_3[G]`, is closed. Then
  `L` is bijective, and `tau_R` is not even pre-injective whenever `a` and `b` do not commute.
- **Literature (not re-read).** Linear surjunctivity over a field `K` is equivalent to stable
  finiteness of `K[G]` (Ceccherini-Silberstein–Coornaert). So an injective `R` would make `F_3[G]`
  not stably finite. No node here depends on this.

## 2. Where it stops

### 2.1 Covered

Every affine three-address ternary rule patched at one pattern that repeats a symbol, on every
placement, over every group. For these rules `ternary-three-address-injective-automata-have-balanced-rules`
reduces to linear surjunctivity over `F_3`.

### 2.2 Patches with three distinct symbols

- **The setup.** Let `p = (p_1, p_2, p_3)` have three distinct symbols. The avoidable-patch
  proposition still applies, with `s` any symbol of `p`: a pattern that avoids `s` is never `p`. So
  an injective rule again forces `L` to be injective.
- **The collision attempt.** Let `L` be bijective, let `d_0` be the preimage `L(d_0) = -epsilon delta_1`,
  and let `d(g) = d_0(h^-1 g)`. Pick a symbol `sigma = p_i`. Fill `x` with `x + d = p` on `hM`, and keep
  `sigma` out of both configurations at every other site.
  - **`x + d`.** Its `sigma`-sites are exactly `{h m_i}`, so it shows `p` only at `h`.
  - **`x` at `h`.** It cannot show `p` there, because `L(d)(h) != 0`.
  - **`x` elsewhere.** It can show `p` only at `g = h m_beta m_i^-1` with `beta != i`. That needs
    `x(h m_beta) = p_i`, which means `d_0(m_beta) = p_beta - p_i`.
- **When some choice of `sigma` has no danger.** Write `e_beta = p_beta - d_0(m_beta)`, the values of
  `x` on `hM`.
  - **The collision holds** unless, for every `i`, some `beta != i` has `e_beta = p_i`.
  - **What that forces.** Then `e = p o pi` for a 3-cycle `pi`. The differences
    `p_beta - p_(pi(beta))` are three nonzero elements of `F_3` summing to `0`, so they are equal.
    So `d_0` is a constant `kappa != 0` on `M`, and `kappa (c_1 + c_2 + c_3) = -epsilon`.
- **The danger case.** Here `x` can show `p` at `h m_beta m_i^-1` only if both other sites of that
  translate of `M` carry the right symbols.
  - **Generic sites.** Where `d = 0`, two symbols avoid `sigma` and one of them avoids the required
    symbol, so the occurrence can be broken.
  - **Forced sites.** Where `d != 0`, or on `hM`, the symbol is forced. The occurrence survives only
    under value coincidences of `d_0` on `M m_i^-1 M`.
- **Status.** No uniform way to break these is known. **Open.**
- **Relation to `constant-background-kills-unit-linear-defect-rules`** (w3-bal-design, Theorems 13
  and 13').
  - **Their method.** A constant background kills the unit case, except for absorbed memory
    translates inside `M ∪ N^-1` that show `p`.
  - **For patches repeating a symbol.** Theorem 1.1 empties that residue over non-commuting memory.
  - **For patches with three distinct symbols.** Their residue (for every symbol `c`, an absorbed
    translate of `M \ P_c`) and the danger case above are two residues of the same unit case.
    Whether a group can meet both at once is not checked here.

### 2.3 Rules far from affine

A rule at Hamming distance at least 2 from every affine rule has no canonical linear part, and
both the avoidable-patch transfer and Theorem 1.1 lose their input. **Open.**

### 2.4 What remains of the census claim

Beyond linear strictness over `F_3`, `ternary-three-address-injective-automata-have-balanced-rules`
now reduces to two classes:
- single patches with three distinct symbols, in the danger case of 2.2;
- rules at distance at least 2 from every affine rule.
