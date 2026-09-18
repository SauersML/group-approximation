---
rg: 2
id: circle-overgroups-of-thompson-t-mixed-identities-proof
kind: route
title: Approximate any circle homeomorphism by an element of T on a fine dyadic grid, then extend each mixed identity to the closure by continuity of word maps
target: circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities
requires: [thompson-t-mixed-identity-problem-is-decidable]
---

The only import is Lemma L2 (T) of
`thompson-t-mixed-identity-decision-procedure-proof`, the route that establishes
`thompson-t-mixed-identity-problem-is-decidable`:

> "Let `P` be a finite partial injection of `D` that preserves cyclic order:
> every three distinct domain points have the same orientation as their images.
> Then some `g in T` extends `P`."

Here `D` is the set of dyadic points of `S^1 = R/Z`. Everything else is
elementary. Write `|p - q|` for the arc distance on `S^1`, and `[p, q]` for the
positively oriented closed arc from `p` to `q`.

## Step 1: Homeo+(S^1) is a topological group

Use `d(f, g) = sup_p |f(p) - g(p)|`. Every `f` is uniformly continuous; let
`ω_f` be its modulus, so `|f(p) - f(q)| <= ω_f(|p - q|)` and `ω_f(δ) -> 0` as
`δ -> 0`.
- *Products.* `d(fg, f'g') <= d(fg, fg') + d(fg', f'g') <= ω_f(d(g, g')) + d(f, f')`.
- *Inverses.* Substitute `p = g(q)`:
  `d(f^-1, g^-1) = sup_q |f^-1(g(q)) - f^-1(f(q))| <= ω_(f^-1)(d(f, g))`.

Both right-hand sides tend to `0`, so multiplication and inversion are
continuous. The metric makes the group Hausdorff.

## Step 2: T is dense (part (A))

Fix `f in Homeo+(S^1)` and `ε > 0`.

1. **A grid.** Choose `δ > 0` with `ω_f(δ) < ε`. Choose dyadic points
   `p_1, ..., p_n` (`n >= 3`) in positive cyclic order with every gap
   `|p_i - p_(i+1)| < δ`, indices mod `n`. The points `f(p_i)` are distinct,
   in positive cyclic order, and each arc `[f(p_i), f(p_(i+1))]` has length
   `< ε`.
2. **Dyadic targets.** Let `η > 0` be less than `ε` and less than half of every
   gap `|f(p_i) - f(p_(i+1))|`. Choose dyadic `q_i` with `|q_i - f(p_i)| < η`.
   The arcs `(f(p_i) - η, f(p_i) + η)` are pairwise disjoint and occur in the
   cyclic order of the `f(p_i)`, so the `q_i` are distinct and in positive
   cyclic order.
3. **An element of T.** The partial injection `p_i -> q_i` preserves cyclic
   order. By Lemma L2 (T), some `t in T` has `t(p_i) = q_i` for all `i`.
4. **Uniform closeness.** The arcs `[p_i, p_(i+1)]` cover `S^1`. Let `p` lie in
   one of them.
   - `t` preserves orientation, so `t(p) in [q_i, q_(i+1)]`.
   - Likewise `f(p) in [f(p_i), f(p_(i+1))]`.
   - Both arcs lie in the `η`-neighbourhood of `[f(p_i), f(p_(i+1))]`, which has
     diameter `< ε + 2η`.

   So `|t(p) - f(p)| < ε + 2η < 3ε`, hence `d(t, f) <= 3ε`.

As `ε` was arbitrary, `T` is dense in `Homeo+(S^1)`.

## Step 3: the closure principle (part (B))

Let `H` be a Hausdorff topological group, `S <= M <= H` with `M ⊆ cl(S)`, and
`w in J_k(S)`. Write `w = c_0 x_(i_1)^(e_1) c_1 ... x_(i_r)^(e_r) c_r` with
`c_j in S`.
- The word map `E_w : H^k -> H`, `(g_1, ..., g_k) -> c_0 g_(i_1)^(e_1) c_1 ... c_r`,
  is a finite composite of projections, inversions, multiplications and
  multiplications by the constants `c_j`. So it is continuous.
- `{1}` is closed because `H` is Hausdorff. So `E_w^-1(1)` is closed.
- `E_w^-1(1) ⊇ S^k`, since `w in J_k(S)`. The closure of `S^k` in `H^k` is
  `cl(S)^k`, which contains `M^k`.

So `w(g) = 1` for every `g in M^k`, that is `w in J_k(M; S)`. The reverse
inclusion `J_k(M; S) ⊆ J_k(S)` holds for every `M ⊇ S`, because `S^k ⊆ M^k`.

## Step 4: circle overgroups (part (C))

By Steps 1 and 2, `H = Homeo+(S^1)` is a Hausdorff topological group with
`cl(T) = H`. Every `M` with `T <= M <= H` satisfies `M ⊆ cl(T)`, and Step 3
applies.

For a conjugate action `T^φ = φ T φ^-1`, with `φ in Homeo(S^1)`: the estimates
of Step 1 hold verbatim in `Homeo(S^1)`, so conjugation by `φ` is a
homeomorphism of `Homeo(S^1)` onto itself. It carries `Homeo+(S^1)`, an index-2
closed subgroup, to itself. So `cl(T^φ) = φ cl(T) φ^-1 = Homeo+(S^1)`.
Step 3 applies again, and `J_k(M; T^φ)` is `J_k(T)` read through the
isomorphism `t -> φ t φ^-1`.

## Step 5: ultrapowers (part (D))

For `w in J_k(S)`, the first-order sentence `∀ x_1 ... ∀ x_k (w(x) = 1)` with
parameters `c_j` from `S` holds in `S`. By Łoś's theorem it holds in `S^I / U`
with the parameters read diagonally. It is a universal sentence, so it holds in
every subgroup of `S^I / U` that contains the parameters, in particular in `M`.

## Step 6: products (part (E))

Evaluation in `∏ M_i` is coordinatewise, and each diagonal constant is `c_j` in
each coordinate. So `w(g)` has `i`-th coordinate `w(g_i)`, where `g_i` is the
`i`-th coordinate tuple, and this is `1` by hypothesis. Subgroups containing the
diagonal inherit this.

## Step 7: blow-ups along irrational orbits (part (F))

Notation is as in (F). Write `K = C ∖ ∪ I_q`. Every `f in M_Q` has a unique
*shadow* `t = σ(f) in T` with `π f = t π`, because `π` is onto and `T` acts
faithfully. `σ` is a homomorphism, and `σ(ρ(t)) = t` for the affine lift `ρ(t)`.
`M_Q` is a group: if `π f = t π` and `π f' = t' π`, then `π f f' = t t' π`,
and gaps go to gaps.

**7a. Germ-freeness.** Let `q` be irrational and `s in T` with `s(q) = q`.
Near `q`, `s` is affine, `s(y) = 2^e y + d` with `d` dyadic, since breakpoints
are dyadic. If `e != 0`, the fixed point `q = d / (1 - 2^e)` is rational. So
`e = 0`, then `d = 0`, and `s` is the identity on a neighbourhood of `q`.
`T` maps irrationals to irrationals, so every point of `Q` is irrational.

**7b. Setup.** Suppose `w in J_k(T)` and `m = (m_1, ..., m_k) in M_Q^k` with
`w(m) != 1`. Write `w(m)` as a product `ℓ_N ... ℓ_1` of letters: constants
`ρ(c)`, with `c in T`, and `m_i^(±1)`. Put `t_i = σ(m_i)`. Then
`σ(w(m)) = w(t) = 1`, since `w in J_k(T)`. Pick `z in C` with `w(m) z != z`, and
put `z_0 = z`, `z_j = ℓ_j z_(j-1)`.

**7c. The moved point lies in a gap.** Suppose `z in K`. Then every `z_j` is in
`K`, since letters map gaps onto gaps. `π(w(m) z) = w(t) π(z) = π(z)`.
- If `π(z)` is not in `Q`, `π` is injective over it, so `w(m) z = z`.
- Otherwise `z` is an endpoint of the gap `I_(π z)`. Since `w(m)` maps that gap
  onto `I_(w(t) π z) = I_(π z)` and preserves orientation, it fixes both
  endpoints.

Either way this is a contradiction. So `z in I_(q_0)` for some `q_0 in Q`, and
`z_j in I_(q_j)` with `q_j = σ(ℓ_j) q_(j-1)`.

**7d. Mirror arcs.** Let `R = {q_0, ..., q_N}`, a finite subset of one
`T`-orbit. For each `r in R` fix `s_r in T` with `s_r(q_0) = r`, taking
`s_(q_0) = 1`. Consider the finitely many elements
`g = s_(σ(ℓ) r)^-1 σ(ℓ) s_r` for letters `ℓ` and `r in R` with `σ(ℓ) r in R`.
Each fixes `q_0`, so by 7a it is the identity near `q_0`. Choose an open arc
`A_(q_0)` around `q_0` so small that:
- every such `g` is the identity on `A_(q_0)`;
- every `s_r` is affine on `A_(q_0)`, and every `σ(ℓ)` is affine on
  `A_r = s_r(A_(q_0))` (possible as the points are irrational, hence not
  breakpoints);
- the arcs `A_r`, `r in R`, are pairwise disjoint.

Then `σ(ℓ)(A_r) = A_(σ(ℓ) r)` whenever `σ(ℓ) r in R`.

**7e. Mirrored letters.** Fix orientation-preserving affine bijections
`φ_r : I_r -> A_r`. For each `i`, define `x_i : S^1 -> S^1` by
`x_i = φ_(t_i r) m_i φ_r^-1` on `A_r` when `r` and `t_i r` lie in `R`, and
`x_i = t_i` elsewhere. By 7d, `t_i(A_r) = A_(t_i r)` in the first case. So
`x_i` agrees with `t_i` off finitely many arcs and maps each such arc onto its
`t_i`-image monotonically. Hence `x_i in Homeo+(S^1)`.

For a constant `c` with `c r in R`, `φ_(c r) ρ(c) φ_r^-1` and `c` are both
orientation-preserving affine bijections `A_r -> A_(c r)`, so they agree.
Hence each letter `ℓ_j` of `w(m)` and the matching letter `λ_j` of `w(x)`
satisfy `λ_j φ_(q_(j-1)) = φ_(q_j) ℓ_j` on `I_(q_(j-1))`. (For `m_i^-1`, invert
the relation for `m_i`.)

**7f. Contradiction.** By induction on `j`, `λ_j ... λ_1 φ_(q_0)(z) = φ_(q_j)(z_j)`.
At `j = N`, `q_N = w(t) q_0 = q_0`, so
`w(x) φ_(q_0)(z) = φ_(q_0)(w(m) z) != φ_(q_0)(z)`. So `w(x) != 1` with
`x in Homeo+(S^1)^k`. That contradicts `w in J_k(Homeo+(S^1); T)`, which is
part (C). Hence `J_k(M_Q; T) ⊇ J_k(T)`, and the reverse inclusion is automatic.

**Where 7 uses irrationality.** Only 7a and the affinity in 7d. At a rational
point `q`, some `g` fixing `q` has slope `!= 1` there. It then cannot preserve a
small arc `A_q`, while it may act on `I_q` in any way that is compatible with a
`T`-action. `∎`

## What this route does not give

It says nothing about overgroups in which `T` is not dense for any Hausdorff
group topology, and nothing about the finite basis question itself. It only
removes from the search space every circle overgroup extending a conjugate of
the standard action, every ultrapower overgroup, and every product of these.
