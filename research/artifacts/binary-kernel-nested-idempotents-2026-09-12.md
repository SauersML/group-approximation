# Nested idempotents from two finite subgroups

Lane `w3-kap-kernel`, 2026-09-12. Supports:
- `nested-idempotents-from-p-regular-intersections-are-equal` (established);
- the open hole `modular-nested-idempotents-equivalent-over-leavitt-units`;
- the route `modular-nested-equivalence-refutes-leavitt-direct-finiteness`.

## 0. Setting

Let `p` be a prime and `G` a group. Write `S = F_p[G]`, and let `t_p : K_0(S) -> Z_p` be
the additive lifted trace of `lifted-trace-detects-finite-subgroup-projectives`. For a
finite subgroup `H` and an idempotent `c` in `M_n(F_p[H])` it takes the value
`dim(c F_p[H]^n) / |H|`, a nonnegative rational that is positive when `c != 0`.

**Defects are nested equivalent idempotents.** Suppose `0 != f < e` are idempotents
(`ef = fe = f`) and `e ~ f`, meaning `xy = e` and `yx = f`. Replacing `x` by `exf` and `y` by
`fye` leaves both products unchanged, so we may take `x in eSf`, `y in fSe`. Put
`A = (1 - e) + x` and `B = (1 - e) + y`. The cross terms vanish, because
`(1 - e) f = 0 = f (1 - e)`. So `AB = 1` and `BA = 1 - (e - f) != 1`. Every one-sided pair
arises this way, with `e = 1`. In the binary invisible problem `e` and `f` may be taken
inside the kernel corner `zSz` of `leavitt-unit-group-algebra-embeds-in-kernel-corner`.

This lane was asked to build such pairs from idempotents supported in different finite
subgroups. Section 2 kills every such pair whose two subgroups meet in a group of order
prime to `p`, whatever subgroup they generate.

## 1. Coset components

**Lemma 1.** Let `H_1, H_2 <= G` be finite, `e in M_n(F_p[H_1])` and `f in M_n(F_p[H_2])`
with `e f = f`, and put `C = H_1 ∩ H_2`. Choose representatives `h_t` of the left cosets
of `C` in `H_1`, with `h_1 = 1`, and write

    e = sum_t h_t eps_t,        eps_t in M_n(F_p[C]).

Then `eps_1 f = f` and `eps_t f = 0` for `t != 1`.

*Proof.* `h_t c f` has support in `h_t H_2`, and distinct cosets `h_t C` lie in distinct
cosets `h_t H_2`: if `h_t H_2 = h_s H_2`, then `h_s^-1 h_t` lies in `H_1 ∩ H_2 = C`. So
`e f = sum_t h_t (eps_t f)` has disjoint supports over the cosets `h_t H_2`. Since `e f = f`
is supported in `H_2`, the coset `t = 1` gives `eps_1 f = f`, and every other coset gives
`eps_t f = 0`. QED

## 2. The theorem

**Theorem 2.** Keep the notation of Lemma 1. Assume that `p` does not divide `|C|`, that
`f <= e`, and that `t_p([e]) = t_p([f])`. Then `e = f`.

*Proof.*
1. **An idempotent between them.** `M_n(F_p[C])` is semisimple, since `p ∤ |C|`. The left
   annihilator `Λ = { x in M_n(F_p[C]) : x f = 0 }` is a left ideal, so
   `Λ = M_n(F_p[C]) (1 - π)` for an idempotent `π`. Then `x in Λ` iff `x π = 0`. From
   `1 - π in Λ` we get `π f = f`. Lemma 1 gives `eps_t in Λ` for `t != 1` and `eps_1 - 1 in Λ`,
   so `eps_t π = 0` and `eps_1 π = π`. Hence `e π = π`.
2. **Upper comparison.** Put `π_1 = π e`. It is idempotent (`π e π e = π (e π) e = π e`) and
   `π_1 <= e`. It is equivalent to `π`: `a = π e` lies in `π S π_1`, `b = π` lies in
   `π_1 S π`, and `ab = π e π = π`, `ba = π π e = π_1`. Since `π_1` and `e` lie in
   `M_n(F_p[H_1])`, additivity gives
   `t_p(e) = t_p(π) + dim((e - π_1) F_p[H_1]^n) / |H_1| >= t_p(π)`, with equality only if
   `e = π_1`.
3. **Lower comparison.** `f π` is idempotent (`f π f π = f (π f) π = f π`) and `f π <= π`,
   using `π f = f`. It is equivalent to `f`: `f · fπ = fπ` and `fπ · f = f`. Both `π` and
   `f` lie in `M_n(F_p[H_2])`, so
   `t_p(π) = t_p(f) + dim((π - f π) F_p[H_2]^n) / |H_2| >= t_p(f)`, with equality only if
   `π = f π`.
4. **Conclusion.** `t_p(e) = t_p(f)` forces `e = π e` and `π = f π`. Then
   `e = π e = f π e = f e = f`. QED

All the lifted traces compared here are rationals given by LFT1, and `Q ∩ Z_p` embeds in
`Z_p`, so the inequalities are taken in `Q`.

## 3. Consequences

- **No mixed defect.** If `BA = I` and `I - AB = e - f != 0` with `e`, `f` as in Theorem 2, then
  `[e] = [e - f] + [f]` and a defect has class `0`, so `t_p(e) = t_p(f)` and `e = f`,
  a contradiction.
- **No proper equivalence.** Equivalent idempotents have equal lifted traces, so `f ~ e`
  forces `e = f`.
- **Infinite joins allowed.** `<H_1, H_2>` may be infinite. This is where Theorem 2 goes
  beyond `mixed-finite-subgroup-defects-need-infinite-generation`, which assumes a finite join
  but no intersection condition. Neither statement implies the other.
- **Binary candidates killed.** Over `F_2` the theorem applies whenever `|H_1 ∩ H_2|` is odd:
  - any two finite subgroups meeting trivially, at any prefix levels;
  - every idempotent from order-3, order-5 or order-7 cyclic constants, including Singer-type
    constants in `GL_4(F_2)`-type blocks, since their intersections with anything have odd
    order.
- **Remark for the ternary lanes.** Over `F_3` it applies whenever `3 ∤ |H_1 ∩ H_2|`, for
  example intersections inside the swap and Klein constants `<w>` and `<w, d>`. Out of this
  lane's scope; noted only.

## 4. What survives

- **Even intersections over F_2.** The left annihilator `Λ` need not be generated by an
  idempotent, and step 1 fails.
  - **Smallest case.** `C = <w>` of order 2, `n = 1`. `F_2[C]` is local with ideals `0`,
    `(1 + w)` and `F_2[C]`. The case `Λ = (1 + w)` allows `eps_1` in `{1, w}` and `eps_t` in
    `{0, 1 + w}`, with `w f = f`. Lemma 1 does not exclude these.
  - **The S_3 constants `<u, v>`.** `F_2[<u, v>]` is the local block
    `F_2[<u, v>] z ≅ F_2[C_2]`, where `z = [1] + [g] + [g^2]` is the kernel idempotent, plus a
    copy of `M_2(F_2)`. Only the local block escapes the semisimple argument.
  - **Klein and dyadic permutation constants.** These survive exactly when their intersection
    contains an involution.
- **Idempotents outside finite subgroups.** Thompson-type supports, where every landed
  exclusion also stops.
- **Support of the equivalence.** `x`, `y`, `H_1` and `H_2` together must generate a subgroup
  that is not locally finite, since group algebras of locally finite groups are directly
  finite.

No candidate pair with even intersection was constructed in this lane.
