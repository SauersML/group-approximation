# Coset-parity closure of Kun--Thom lamp submodules

Lane `w4-lamp-closure`, 2026-09-12. Handwritten; nothing run. Decides the smallest test of
`kun-thom-wreath-lamp-quotient-nonsurjunctive` (Example 5.4 of
`kun-thom-lamp-quotient-hosts-2026-09-12.md`) and isolates the closure that matters.

## 0. Two closures

`P = F_2[G/Gamma]`, `Gamma <= G`. For a `G`-submodule `U <= P`:

- the **permutation closure** `U-bar` is the intersection of `ker(phi)` over all `G`-maps
  `phi : P -> F_2[Y]` (`Y` a `G`-set) with `phi(U) = 0`; `U` is **closed** iff `U = U-bar`
  (`residually-permutational-lamp-extensions-are-surjunctive`);
- the **coset-parity closure** `U^c` is the same but only over the coset projections
  `pi_S : P -> F_2[G/S]`, `e_(g Gamma) -> e_(g S)`, one per subgroup `S >= Gamma` with
  `pi_S(U) = 0`.

Coset projections are permutation maps, so using **fewer** maps gives a **bigger** intersection:

    U  <=  U-bar  <=  U^c.

**Lemma 0.1 (coset parity suffices).** If `U = U^c` then `U = U-bar` and `W/U` is surjunctive.
*Proof.* `U = U^c` forces `U = U-bar` by the sandwich, and then
`P/U` embeds in `prod_S F_2[G/S]` through the `pi_S` with `pi_S(U)=0` (their common kernel is
`U^c = U`). Each `F_2[G/S]` is a permutation module, so `P/U` is residually permutational and
`W/U` is surjunctive by `residually-permutational-lamp-extensions-are-surjunctive`. QED

So a lamp quotient can be proved surjunctive using only the concrete fibre-parity maps `pi_S`,
with no Hecke cancellation. `U^c` is idempotent (`(U^c)^c = U^c`), so `W/U^c` is surjunctive for
**every** `U`: the only room for a counterexample is the gap `U-bar / U` (a fortiori `U^c / U`).

## 1. The commutator generator

Fix `a, b in G`. Put

    v = (1+a)(1+b) e_Gamma,   w = (1+b)(1+a) e_Gamma,   m = b^-1 a^-1 b a,   U = F_2[G] v.

Both `v, w` are fibre-even when `a, b in N`. `w + v = e_(ab Gamma) + e_(ba Gamma)`, and
`(ab+ba)c = 0` for a vector `c` means exactly `m c = c`. Example 5.4 asks whether `w in U-bar`.

**Theorem 1.2 (coset closure of the commutator generator is a subgroup membership).**

    w in U^c   <=>   m in <Gamma, ab, a^-1 b>.

Write `S_0 = <Gamma, ab, a^-1 b>`. In particular, **if `m notin S_0` then `w notin U-bar`**:
the reversed product is not in the permutation closure, so this generator does not enlarge the
closure through `w`.

*Proof.* For `S >= Gamma`, `pi_S(U) = 0` iff `pi_S(v) = 0` (`pi_S` is `G`-equivariant and `U` is
cyclic on `v`). Now

    pi_S(v) = e_S + e_(aS) + e_(bS) + e_(abS),
    pi_S(w) = e_S + e_(aS) + e_(bS) + e_(baS).

`pi_S(v) = 0` needs the four cosets to cancel in two pairs. The pairings are:
- **(I)** `aS = bS` and `abS = S`, i.e. `ab in S` and `a^-1 b in S`;
- **(II)** `a in S` (then `S=aS`, `bS=abS`);
- **(III)** `b in S` (then `S=bS`, `aS=abS`).
(If three or four of the cosets coincide it is a sub-case of II and III.)

In (II) and (III) the same coincidences give `pi_S(w) = 0` directly.

In (I), `pi_S(w) = e_S + e_(aS) + e_(aS) + e_(baS) = e_S + e_(baS)`. Since `ab in S`,
`ba = (ab) m` gives `baS = S` iff `m in S`. So `pi_S(w) != 0` iff `m notin S`.

(<=) If `m notin S_0`, take `S = S_0`: it is type (I), `pi_(S_0)(v) = 0`, and `pi_(S_0)(w) != 0`,
so `w notin ker pi_(S_0) >= U^c`, i.e. `w notin U^c`.

(=>) If `m in S_0`, then every `S >= Gamma` with `pi_S(v) = 0` gives `pi_S(w) = 0`: types II, III
are immediate, and a type-(I) `S` contains `S_0`, hence `m`, hence `baS = S`, hence `pi_S(w)=0`.
So `w in U^c`. QED

## 2. The smallest test is negative for free generators

`m notin S_0` is a membership question in `G`. It holds whenever `a, b` are chosen so that
`S_0 cap <a,b> = <ab, a^-1 b>`, because in the free group `F(a,b)`:

**Lemma 2.1.** `m = b^-1 a^-1 b a notin <ab, a^-1 b>` in `F(a,b)`.
*Proof.* Stallings graph of `H = <ab, a^-1 b>`: after folding it has two vertices `*, u` with
`a`-edges `* -> u` and `u -> *` and a single `b`-edge `u -> *`. Reading `m = b^-1 a^-1 b a` from
`*`: `b^-1` goes `* -> u`, `a^-1` goes `u -> *`, and then `b` has no outgoing edge at `*`. The
read fails, so `m notin H`. QED

`N = EL_r(R)` (`r >= 3`) is not virtually solvable and contains nonabelian free subgroups; picking
`a, b` inside one with `<a,b> cap Gamma = 1` and `<a,b> cap S_0 = <ab,a^-1 b>` gives `m notin S_0`,
so by Theorem 1.2 **`w notin U-bar`**. The commutator generator, for such `a, b`, is coset-separated
from its reversal: Example 5.4 resolves negatively, like the single fibre pairs of Example 3.4.

## 3. Where non-closedness must live

A non-closed `U` (the only route to a counterexample) needs an element `x in U-bar \ U`. Theorem
1.2 shows the reversed commutator cannot be such an `x` unless `m in S_0` for **every** presentation
`S_0`, i.e. the inseparability `m in <Gamma, ab, a^-1 b>` holds. For `a, b in N` with non-closed
behaviour one therefore needs `ab, a^-1 b` to generate (with `Gamma`) a subgroup already containing
the commutator `m` while `m` is detected by some Hecke operator with cancellation (Lemma 5.3) but by
no coset projection. No such pair is exhibited here, and `m in <Gamma, ab, a^-1 b>` is the exact
residue for the weight-four commutator class. Heavier generators (weight `>= 4` whose relations no
`pi_S` sees even after cancellation) remain the only candidates.
