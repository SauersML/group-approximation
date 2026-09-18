---
rg: 2
id: fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff
kind: claim
title: The worst-pair rate above p_c plus the conditional chemical slope of the critical worst pairs times log(t/p_c) is at least log gr, with equality on trees
distinct_from:
  fpbs-integrated-sensitivity-iff-subscale-chemical-saturation: that is an equivalence for the walk-averaged rate lambda and needs chemical slope o(1/epsilon) for all small epsilon; this bounds the extrinsic worst-pair rate gamma from one critical worst pair per radius and needs slope below log gr / log(t/p_c) at a single t
  fpbs-intrinsic-rates-log-lipschitz-in-parameter: that thins chemical-radius truncations summed over a ball and gives K_* >= log gr / (2 log(t/p_c)); this thins at the p_c-minimisers of tau, which removes the factor 2 and gives a conditional version
  fpbs-worst-pair-connectivity-rate-kernel: that proves (K) implies p_c < p_u and records gamma(p_c) >= log gr as recalled; this proves gamma(p_c) >= log gr from sharpness alone and transfers it to every t > p_c at a chemical-length cost
  fpbs-uniform-chemical-stretch-above-pu: that is an unconditional uniform stretch bound above p_u, expected false on planar tilings; this is a conditional slope of one pair per radius, and only an inequality
---

**ESTABLISHED.** Proof in `fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff-proof`.

**Setting.** As in `fpbs-worst-pair-connectivity-rate-kernel`: `G = Cay(Gamma,S)`
for a finitely generated nonamenable `Gamma`, `gr > 1`,
`kappa_p(n) = min_(v in B_n) tau_p(o,v)` and
`gamma(p) = lim_n -(1/n) log kappa_p(n)`. `d_omega` is chemical distance in
the open subgraph. For `n >= 1` let

```text
A_n = { v in B_n : tau_(p_c)(o,v) = kappa_(p_c)(n) }       (critical worst pairs, nonempty)
s_t(v,R) = P_t( d_omega(o,v) <= R | o <-> v )
l(t) = inf{ L >= 0 : limsup_n (1/n) log max_(v in A_n) s_t(v, L n) = 0 }   (inf of the empty set = +infinity)
```

`l(t)` is the **conditional chemical slope of the critical worst pairs** at `t`:
the least `L` such that, along some sequence of radii, some critical worst pair
`v_n in A_n` is, given `o <-> v_n` at level `t`, joined by an open path of
length at most `L n` with conditional probability `e^(-o(n))`.

**Theorem.**

1. *(Critical worst pairs.)* `kappa_p(n) <= gr^(-n)` for every `n >= 1` and
   every `p <= p_c`. So `gamma(p_c) >= log gr`. This proves the input that
   `fpbs-worst-pair-connectivity-rate-positive-above-pc-universal` records as
   recalled from Hutchcroft, using only subcritical sharpness.
2. *(Trade-off.)* For every `t in (p_c,1]`,

   ```text
   gamma(t) + l(t) log(t/p_c)  >=  gamma(p_c)  >=  log gr .
   ```

3. *(Sufficient condition for (K).)* If some `t > p_c` has
   `l(t) < log(gr) / log(t/p_c)`, then `gamma(t) > 0`, and so `p_c < p_u`.
4. *(Forced slope in the uniqueness phase.)* If `t > p_c` and `omega_t` has a
   unique infinite cluster a.s., then `gamma(t) = 0` and
   `l(t) >= log(gr)/log(t/p_c)`. Quantitatively, `t >= p_c gr^(1/l(t))`.
   Under a hypothetical collapse `p_c = p_u` this holds at every `t > p_c`, so
   `l(p_c + epsilon) >= p_c log(gr) / epsilon` for every `epsilon > 0`.
5. *(Unconditional stretch, factor 2 gained.)* For `t > p_c`, every linear
   stretch constant `K` at `t` (item 4 of `fpbs-intrinsic-l2-rate-closed-zero-set`)
   has `K >= log(gr)/log(t/p_c)`. This improves item 4 of
   `fpbs-intrinsic-rates-log-lipschitz-in-parameter` by a factor 2.
6. *(Equality on trees.)* On `T_d`, `d >= 3`, `A_n = S_n`, `l(t) = 1`,
   `gamma(t) = -log t` and `gamma(p_c) = log(d-1) = log gr`. So item 2 holds
   with equality at every `t in (p_c,1]`.

**Reading.** Any collapse must make the critical worst pairs, once connected
at `p_c + epsilon`, use chemical length at least about
`p_c log(gr) n / epsilon` with all but exponentially small conditional
probability. Their extrinsic distance is at most `n`. Item 2 is one
inequality, so item 3 and the first half of item 4 are contrapositives of
each other. The content is the constant, which item 6 shows is sharp.
