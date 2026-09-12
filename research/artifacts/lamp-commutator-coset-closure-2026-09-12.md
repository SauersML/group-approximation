# Coset-parity closure of Kun--Thom lamp submodules

Lane `w4-lamp-closure`, 2026-09-12. Handwritten; nothing run. Decides the smallest test of
`kun-thom-wreath-lamp-quotient-nonsurjunctive` (Example 5.4 of
`kun-thom-lamp-quotient-hosts-2026-09-12.md`) and isolates the closure that matters.

**Correction (w3-vf-nonlinear, Section 21 of its verification artifact).** The first version of
Theorem 1.2 (330d3b39cb) claimed `w in U^c <=> m in S_0`. That is false: pairing (P_b), `b in S`,
does not force `pi_S(w) = 0`. The corrected theorem has a second membership. The direction used for
the negative resolution (`m notin S_0 => w notin U-bar`) was and is correct.

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
*Proof.* `U = U^c` forces `U = U-bar` by the sandwich, and `P/U` embeds in `prod_S F_2[G/S]`
through the `pi_S` with `pi_S(U) = 0`, whose common kernel is `U^c = U`. Each `F_2[G/S]` is a
permutation module, so `P/U` is residually permutational and `W/U` is surjunctive by
`residually-permutational-lamp-extensions-are-surjunctive`. QED

`U^c` is idempotent (`(U^c)^c = U^c`), so `W/U^c` is surjunctive for **every** `U`. The only room for
a counterexample is the gap `U-bar / U`, and a fortiori `U^c / U`.

## 1. The commutator generator

Fix `a, b in G`. Put

    v = (1+a)(1+b) e_Gamma,   w = (1+b)(1+a) e_Gamma,   m = b^-1 a^-1 b a,   U = F_2[G] v,
    S_0 = <Gamma, ab, a^-1 b>,   S_1 = <Gamma, b>.

Both `v, w` are fibre-even when `a, b in N`. Example 5.4 asks whether `w in U-bar`.

**Theorem 1.2 (corrected).**

    w in U^c   <=>   m in S_0   and   a^-1 b a in S_1.

So **if `m notin S_0` or `a^-1 b a notin S_1`, then `w notin U-bar`**.

*Proof.* For `S >= Gamma`, `pi_S(U) = 0` iff `pi_S(v) = 0`, by equivariance and cyclicity. Now

    pi_S(v) = e_S + e_(aS) + e_(bS) + e_(abS),
    pi_S(w) = e_S + e_(bS) + e_(aS) + e_(baS).

`pi_S(v) = 0` iff the four cosets cancel in pairs, that is, iff one of:
- **(P_a)** `a in S` and `b^-1 a b in S` (`S = aS`, `bS = abS`). Then `aS = S` and `baS = bS`, so
  `pi_S(w) = 0`.
- **(P_b)** `b in S` (`S = bS`, `aS = abS`). Then `pi_S(w) = e_(aS) + e_(baS)`, zero iff
  `a^-1 b a in S`.
- **(P_ab)** `ab in S` and `a^-1 b in S` (`S = abS`, `aS = bS`). Then `pi_S(w) = e_S + e_(baS)`, and
  `ba = (ab) m` gives `baS = S` iff `m in S`.

Each formula uses only its own pairing's conditions, so it holds whenever that pairing does.
`w in U^c` iff every `S` satisfying some pairing has `pi_S(w) = 0`. (P_a) never obstructs. The
subgroups satisfying (P_b) are those containing `S_1`, and all contain `a^-1 b a` iff `S_1` does. The
subgroups satisfying (P_ab) are those containing `S_0`, and all contain `m` iff `S_0` does. QED

**Example 1.3 (the second condition is needed).** `G = S_3`, `Gamma = 1`, `a = (12)`, `b = (13)`.
`ab` is a 3-cycle, so `S_0 = A_3 ni m`. But `S = <b>` satisfies (P_b), and
`a^-1 b a = (23) notin <b>`, so `pi_S(w) = e_(aS) + e_(baS) != 0` and `w notin U^c`.

## 2. The smallest test is negative for free generators

**Lemma 2.1.** In `F(a,b)`, `m = b^-1 a^-1 b a notin <ab, a^-1 b>`, and `a^-1 b a notin <b>`.
*Proof.* Stallings graph of `H = <ab, a^-1 b>`: after folding it has two vertices `*, u`, `a`-edges
`* -> u` and `u -> *`, and a single `b`-edge `u -> *`. Reading `m = b^-1 a^-1 b a` from `*`:
`b^-1` goes `* -> u`, `a^-1` goes `u -> *`, and then `b` has no outgoing edge at `*`. The read
fails, so `m notin H`. The word `a^-1 b a` is reduced and is not a power of `b`. QED

`N = EL_r(R)` (`r >= 3`) contains nonabelian free subgroups. Pick `a, b` in one with
`<a,b> cap S_0 = <ab, a^-1 b>`. Then `m notin S_0`, so by Theorem 1.2, **`w notin U-bar`**. Example
5.4 resolves negatively for such `a, b`, like the single fibre pairs of Example 3.4. The intersection
hypothesis is the one point not proved for all pairs.

## 3. Where non-closedness must live

A non-closed `U`, the only route to a counterexample, needs an element `x in U-bar \ U`. By Theorem
1.2 the reversed commutator is such an `x` only if **both** `m in <Gamma, ab, a^-1 b>` and
`a^-1 b a in <Gamma, b>`, while some Hecke operator with cancellation (Lemma 5.3 of the host
artifact) still separates `w` from `U`. No such pair is exhibited here. Heavier generators, of weight
at least four whose relations no coset projection sees, remain the only candidates.
