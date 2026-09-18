---
rg: 2
id: natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots
kind: claim
title: The natural Q x| <2> lies in the Röver–Nekrashevych product host 2V_H exactly when the self-similar group H contains the binary odometer together with a root of every odd order, and such an H is never contracting, never of polynomial activity, and never finitely generated affine
requires:
  - affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q
distinct_from:
  affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q: that proves the natural copy is in no 2V_H with H a finitely generated subgroup of Aff(Q); this is the exact criterion for EVERY self-similar H <= Aut(T_2), which turns the host question into one question about self-similar groups.
  dilated-registers-are-sealed: that treats register copies of Q; here Q acts through 2-adic translations on colour 1 and the dyadic register of colour 2, and the odd primes sit in the coefficient group.
  rationals-embed-in-binary-leavitt-unit-group: that asks for Q inside one finitely presented simple unit group; this asks for the odd roots of one element, the odometer, inside a self-similar coefficient group, where the dilation is then free.
---

**ESTABLISHED** by `natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots-proof` (lane bh-free-16, 2026-09-18;
elementary; not reviewed; no priority claimed).

## Setting

As in `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q`:
- **The space.** `X = C × C` is read as `{0,1}^Z`. Colour 1 holds the digits at positions `>= 0`, colour 2 those at
  positions `< 0`.
- **The natural action.** `Q_2` acts by addition with carries upward, and the shift `u` is multiplication by 2. This
  is the natural faithful action of `Q ⋊ ⟨2⟩`.
- **The host.** `H <= Aut(T_2)` is any self-similar group, acting on colour 1 and fixing every colour-2 edge with
  restriction itself. `2V_H` is the topological full group of the Zappa–Szép groupoid.
- **Translations.** `T_c(x) = x + c` on `Z_2`. `T_1` is the binary odometer.

## Theorem

1. **Criterion.** The natural copy of `Q ⋊ ⟨2⟩` lies in `2V_H` if and only if `T_1 ∈ H` and `T_1` has an `m`-th
   root in `H` for every odd `m`. Equivalently, `T_c ∈ H` for every `c ∈ Z_(2)`. The roots of `T_1` in `Aut(T_2)` are
   exactly the `T_(1/m)`, with `m` odd.
2. **One odd denominator per prime suffices.** It is enough that, for every odd prime `q`, `H` contains some
   translation `T_c` whose `c` has denominator exactly `q`.
   - Taking sections then gives `T_1`.
   - Bézout gives `T_(1/q)`.
   - Products give all of `Z_(2)`.
3. **Necessary shape of H.** Such an `H`:
   - is not contracting, since its nucleus contains translations of every odd denominator;
   - is not of polynomial activity in Sidki's sense, since `T_(1/m)` for `m > 1` has a nontrivial section at every
     vertex;
   - is not a finitely generated subgroup of `Aff(Z_2)` with rational coefficients (by the node above).
4. **Host side.** Suppose `H` is also of type `F_n` and the groupoid of `2V_H` satisfies Steps A–D of the affine
   node's proof: pseudo-freeness, effectiveness and Hausdorffness, and essential principality. Then Li's
   Example ex:ZS (III) and Matui's simplicity theorem, used there verbatim, make `2V_H` an `F_n` simple group
   containing `Q ⋊ ⟨2⟩`. The copy is `⟨u, T_c × id : c ∈ Z_(2)⟩`.

**So** Boone–Higman for `Q ⋊ ⟨2⟩` through this host family is equivalent to one question about self-similar groups:

> Is there a finitely presented (or `F_∞`) self-similar group of binary tree automorphisms, satisfying Steps A–D,
> in which the binary odometer is divisible by every odd integer?

The dilation costs nothing here: it is the shift `u ∈ 2V`. All the difficulty is the odd roots of one element.

## Lesson for general BH

**In product hosts the dilation is free and the primes live in the coefficient group.** The two-coordinate
product `2V_H` splits the natural `Q ⋊ ⟨2⟩` cleanly:
- the dyadic part and the dilation sit in `2V`, as the colour-2 register and the shift;
- the odd part is exactly `C_H(T_1) ∩ Z_(2)`.

So "host for `Q ⋊ ⟨2⟩`" becomes "self-similar group in which one element, the odometer, is odd-divisible". Three
facts point the search in one direction:
- the necessary conditions exclude contracting, bounded and polynomial automata and f.g. affine groups;
- `dilated-registers-are-sealed` excludes register designs in these hosts;
- divisibility needs exponential-activity, non-contracting coefficient groups of type `F_n`, which is the class
  where Li's finiteness theorem is the only tool.

The same template, "dilation from the Thompson layer, divisibility from the coefficient group", is how general BH
hosts should split the input: geometry in the full group, arithmetic in the self-similar group.
