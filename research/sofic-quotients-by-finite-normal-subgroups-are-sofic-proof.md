---
rg: 2
id: sofic-quotients-by-finite-normal-subgroups-are-sofic-proof
kind: route
title: Pass a sofic approximation to the orbit set of the finite kernel
target: sofic-quotients-by-finite-normal-subgroups-are-sofic
requires: []
---

**Hamming form of soficity.** For every finite `S` in `H` and `delta > 0`
there is a map `sigma : H -> Sym(n)` with:

- `sigma(1) = id`;
- `sigma(ab) = sigma(a) sigma(b)` outside a `delta`-fraction of points whenever
  `a`, `b` and `ab` lie in `S`;
- at most `delta n` fixed points for `sigma(a)`, when `a` is in `S \ {1}`.

**Setup.** Fix a finite `Fbar` in `H/M` and `eps > 0`.

- Choose lifts `F` in `H` and put `S = (M u F u F^-1)^4`.
- Take `sigma` as above with `delta` small.
- A point `x` is **good** if `sigma(ab) x = sigma(a) sigma(b) x` for all `a`,
  `b`, `ab` in `S`, and `sigma(a) x != x` for all `a` in `S \ {1}`. The bad
  points have density at most `(|S|^2 + |S|) delta`.
- A point `x` is **very good** if `sigma(m) x` is good for every `m` in `M`.
  The complement has density at most `|M|` times the bad density.

1. **Orbits.** For very good `x` put `O(x) = {sigma(m) x : m in M}`.
   - `|O(x)| = |M|`. Suppose `sigma(m) x = sigma(m') x`. Apply `sigma(m'^-1)`;
     goodness at `x` gives `sigma(m'^-1 m) x = x`, so `m = m'`.
   - For `y = sigma(m) x`, goodness at `x` gives
     `O(y) = {sigma(m'm) x} = O(x)`, and every point of `O(x)` is very good.
   - So the very good points split into disjoint orbits of common size `|M|`.
     Let `Omega` be the set of these orbits, with uniform measure. This is the
     push-forward of uniform measure on the very good points.
2. **Quotient maps.** For `gbar` in `Fbar` with lift `g`, put
   `tau(gbar) O(x) = O(sigma(g) x)` when `x` and `sigma(g) x` are very good,
   and complete arbitrarily to a permutation of `Omega`.
   - *Well defined on orbits.* For `y = sigma(m) x`,
     `sigma(g) y = sigma(gm) x = sigma(g m g^-1) sigma(g) x`, which lies in
     `O(sigma(g) x)`.
   - *Independent of the lift.* `sigma(g m_0) x = sigma(g) sigma(m_0) x` lies in
     the same orbit, by the previous line.
   - *Injective.* If `sigma(g) x' = sigma(m) sigma(g) x`, apply `sigma(g^-1)`;
     goodness at `x'` and at `x` gives `x' = sigma(g^-1 m g) x`, which lies in
     `O(x)`.
   - The partial map is defined off a set of density `O(|M| |S|^2 delta)`.
3. **Almost multiplicative.** Take `gbar`, `hbar` and `gbar hbar` in `Fbar`,
   with lifts `g`, `h` and `k`. Then `k = g h m_1` for some `m_1` in `M`, and on
   very good orbits

   ```text
   tau(gbar) tau(hbar) O(x) = O(sigma(gh) x) = O(sigma(k) x) = tau(gbar hbar) O(x).
   ```

4. **Free.** Let `cbar != 1` with lift `c`, so `c` is not in `M`. If
   `tau(cbar) O(x) = O(x)`, then `sigma(c) x = sigma(m) x` for some `m` in `M`.
   Goodness at `x` gives `sigma(m^-1 c) x = x` with `m^-1 c` in `S \ {1}`, which
   goodness forbids. So `tau(cbar)` fixes no very good orbit.

Choose `delta` small relative to `eps`, `|M|` and `|S|`. The maps `tau` then
form an `eps`-approximation of `Fbar`, so `H/M` is sofic. Every product used in
steps 1–4 is a word of length at most 4 in `M u F u F^-1`, so it lies in `S`.
