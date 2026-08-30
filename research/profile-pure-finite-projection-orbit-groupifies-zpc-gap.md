---
rg: 2
id: profile-pure-finite-projection-orbit-groupifies-zpc-gap
kind: claim
title: One finite profile-pure projection orbit groupifies a perfect ZPC quantum gap
distinct_from:
  finite-readable-translate-algebra-groupifies-zpc-gap: that assumes the whole readable translate algebra is finite dimensional and uses one of its atom orbits; this needs only one nonzero projection with a finite conjugacy orbit and a definite readable profile at every orbit point.
  zpc-readable-control-freezing-to-lcs: that asks for an invariant readable branch carrying one fixed linear-system menu; this permits a moving finite orbit and a different active menu on every orbit point.
  finite-invariant-partition-only-reduces-irs-to-fiber-irs: that uses only a finite measurable partition and retains a fiber IRS character; this kills all atomwise verifier rows in an ordinary finite-index stabilizer quotient and uses the strict game gap.
---

Let `G` be a finite controlled-linear tailored game with a perfect ZPC-IRS
strategy and

```text
omega*(G)<1.                                             (PPO1)
```

Use the faithful stabilizer-character GNS representation `(M,tau,pi)`, put
`q_-=(1-pi(J))/2`, and let `Q_G` and the finite-dimensional joint readable
spectral algebra `D_0` be as in
`finite-readable-translate-algebra-groupifies-zpc-gap`. Assume there is a
nonzero projection

```text
0!=p_0 in q_- M q_-                                    (PPO2)
```

such that its conjugacy orbit

```text
T={pi(g)p_0 pi(g)^*:g in Q_G}                           (PPO3)
```

is finite and profile-pure: for every `p_t in T` there is a joint readable
atom `E_(r(t)) in D_0` with

```text
p_t <= E_(r(t)).                                        (PPO4)
```

The projections in `T` are not required to be minimal, mutually orthogonal,
or contained in a finite-dimensional invariant algebra. Their ranges may
overlap.

Let

```text
H={g in Q_G:pi(g)p_0 pi(g)^*=p_0}.
```

Choose `x_t in Q_G` with `p_t=pi(x_t)p_0pi(x_t)^*`. For every verifier row
active at the profile `r(t)`, substitute the readable signs and normalize its
unreadable word as `c_(t,a)` so acceptance is `c_(t,a)=1`. Put

```text
h_(t,a)=x_t^(-1)c_(t,a)x_t in H,
K_T=H / <<h_(t,a):t in T, a active at r(t)>>_H.         (PPO5)
```

Then `K_T` is finitely presented, the image of `J` is a nontrivial central
involution, and `K_T` is not hyperlinear. Thus a single finite
profile-pure projection orbit is enough; no finiteness or atomicity of the
full readable translate algebra is required.
