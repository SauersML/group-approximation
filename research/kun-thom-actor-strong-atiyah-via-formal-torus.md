---
rg: 2
id: kun-thom-actor-strong-atiyah-via-formal-torus
kind: claim
title: The torsion-free characteristic-zero Kun--Thom actor satisfies Strong Atiyah in every number of variables, via the formal torus
distinct_from:
  two-variable-kun-thom-actor-satisfies-strong-atiyah: that proves the case d = 2, where the acting congruence group is free and the locally indicable extension theorem applies; this proves every d, including d >= 3 where the whole group has property (T), by a residual chain of torsion-free p-adic analytic quotients built from the formal torus.
  p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah: that covers subgroups of one torsion-free compact p-adic analytic group; this covers subgroups of the infinite-dimensional pro-p group GL_r^1(Z_p[[u_1..u_d]]) semidirect SL_d^1(Z_p), which is only an inverse limit of such groups, and places the Kun--Thom actor inside it.
  char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup: that constructs the torsion-free finite-index subgroup H; this proves Strong Atiyah over C for H.
  raag-out-and-mapping-class-virtually-strong-atiyah: that is Fisher--Ng's application of the chain method to Out(A_Gamma) and mapping class groups through Torelli-type filtrations; this applies the same approximation input to the Kun--Thom actor through the u-adic filtration of a formal power series ring.
artifacts:
  - experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.py
  - experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.out
---

**ESTABLISHED** by [[kun-thom-actor-atiyah-formal-torus-proof]].

**Setting.** Let `d >= 1`, `r >= 2`, let `p >= 3` be prime and
`R = Z[x_1^(+-1),...,x_d^(+-1)]`. As in
[[char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup]]:

```text
G_0 = EL_r(R) semidirect SL_d(Z),          alpha_A(x^v) = x^(A v),
K   = ker( EL_r(R) -> GL_r(F_p) )          (evaluate at x = 1, reduce mod p),
Gamma_d(p) = ker( SL_d(Z) -> SL_d(F_p) ),  H = K semidirect Gamma_d(p).
```

**The formal torus.** Let `Lambda = Z_p[[u_1,...,u_d]]` with maximal ideal
`m = (p, u_1, ..., u_d)`. For `A in SL_d(Z_p)` let `sigma_A` be the continuous
ring automorphism with

```text
sigma_A(u_i) = prod_j (1 + u_j)^(A_ji) - 1          (binomial series),
```

and put

```text
W_(r,d,p) = ( I + M_r(m) ) semidirect Gammahat_d(p),
Gammahat_d(p) = ker( SL_d(Z_p) -> SL_d(F_p) ),       (g, A)(g', A') = (g sigma_A(g'), A A').
```

## Statement

1. **Embedding.** `iota(x_i) = 1 + u_i` defines an injective ring map
   `R -> Lambda` with `iota o alpha_A = sigma_A o iota`. The map
   `(M, A) -> (iota(M), A)` is an injective homomorphism `H -> W_(r,d,p)`.
2. **Residual structure.** `W_(r,d,p)` is torsion-free. The kernels of
   `W_(r,d,p) -> Q_n = GL_r^1(Lambda/(u)^n) semidirect Gammahat_d(p)` form a
   descending chain of normal subgroups with trivial intersection. Each `Q_n`
   is a torsion-free compact `p`-adic analytic pro-`p` group.
3. **Strong Atiyah.** Every countable subgroup of `W_(r,d,p)` satisfies the
   Strong Atiyah conjecture over `C`. In particular `H` does, for every
   `d >= 1`, `r >= 2`, `p >= 3`, and `k[H]` is a domain for every field `k` of
   characteristic `0`.
4. **The ambient actor.** For every finite matrix `A` over `C[G_0]`,
   `rk_(N(G_0))(A)` lies in `(1/[G_0 : H]) Z`, with
   `[G_0 : H] = |SL_r(F_p)| |SL_d(F_p)|`.

## Why this is a new class

For `r, d >= 3`, `H` has property (T): `EL_r(R)` has (T) by
Ershov--Jaikin-Zapirain (the program's Kazhdan input, see
[[el-r-polynomial-robust-spectral-gap]]), `SL_d(Z)` has (T), and (T) passes to
extensions and to finite-index subgroups. So:

* every elementary amenable quotient of a finite-index subgroup of `H` is
  finite. A torsion-free elementary amenable quotient is then trivial, so `H`
  is not residually torsion-free elementary amenable, and Schick's theorem does
  not apply;
* `H` has no infinite locally indicable quotient, so the
  Jaikin-Zapirain--Lopez-Alvarez extension theorem cannot remove the acting
  group. This is exactly where the `d = 2` proof stopped;
* the natural closure `W_(r,d,p)` is not a `p`-adic analytic group. It contains
  the closed abelian subgroup `I + (u) E_12`, which is isomorphic to the
  additive group `(u)`, a product of infinitely many copies of `Z_p`. So the
  Farkas--Linnell import does not apply directly. Whether `H` embeds in some
  other compact `p`-adic analytic group is not decided here.

**Mechanism.** The acting group enters the chain.
* Monomial substitutions fix the point `x = 1`, so they preserve the powers of
  the augmentation ideal `(x_1 - 1, ..., x_d - 1)`.
* After `p`-adic completion they act as continuous automorphisms of the formal
  torus `Z_p[[u]]`, and truncation modulo `(u)^n` is equivariant, with compact
  `p`-adic analytic congruence quotients.
* The `d = 2` proof specialized the variables to independent `p`-adic units.
  That map is injective but not equivariant, which is why it needed a free
  acting group.

## What it changes

* **Vertex input for the nonsofic doubles.** The Attempts of
  `nonsofic-group-satisfying-strong-atiyah` record: "No torsion-free rigid pair
  with `G` satisfying Strong Atiyah is recorded", and for the
  characteristic-zero actors with `d >= 3` "there is no locally indicable
  quotient". This node supplies Strong Atiyah for the vertex groups.
  [[char-zero-kun-thom-double-reduces-nonsofic-atiyah-to-edge]] uses it to reduce
  that target to `strong-atiyah-kazhdan-edge-amalgam-permanence`.
* **Host status.** For all `d`, the characteristic-zero actor is not a host for
  a counterexample to Strong Atiyah or to the zero-divisor conjecture in
  characteristic `0`.

## Model test

* **Recovers `d = 2`.** Item 3 with `d = 2` is
  [[two-variable-kun-thom-actor-satisfies-strong-atiyah]], by a different proof.
* **Fails where it must, at `p = 2`.** `-I in K`, so `H` has an element of order
  two whose averaging projection has trace `1/2`. In the proof the only step
  that uses `p >= 3` is torsion-freeness modulo `(u)`, namely `CS(1,r,p)` and
  `Gammahat_d(p)`. The formal step, that `(u)`-congruence elements have no
  torsion, holds for all `p`. Check 6 of the script exhibits `-I` for `p = 2`.
* **Script.** `experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.py`
  checks, modulo `(3^6, u^4)` with `d = r = p = 3`:
  - the intertwining `iota o alpha_A = sigma_A o iota`, with a negative control
    (the transpose does not intertwine);
  - the cocycle `sigma_A sigma_B = sigma_AB`;
  - the homomorphism property on random elements of `H`;
  - strictness of the chain;
  - the formal no-torsion step for `p = 3` and `p = 2`;
  - the `p = 2` failure.

  All checks pass (`check_formal_torus.out`, under a second).

## Trust surface

The approximation input is Jaikin-Zapirain's theorem, as stated in Fisher--Ng,
arXiv:2606.19606, Theorem 2.5 and Corollary 2.6: a finitely generated group with a
residual normal chain whose quotients are torsion-free, sofic and satisfy
Strong Atiyah over `C` satisfies Strong Atiyah over `C`. The `p`-adic analytic
input is [[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]]. Both
were read at statement level (Fisher--Ng html, 2026-09-17). Everything else is
proved in the proof node.
