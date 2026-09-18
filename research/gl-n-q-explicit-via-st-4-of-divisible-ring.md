---
rg: 2
id: gl-n-q-explicit-via-st-4-of-divisible-ring
kind: route
title: The single finitely presented group St_4(D) of the divisible ring engine contains GL_n(Q) for every n
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - one-steinberg-group-contains-every-gl-n-q
  - finitely-presented-divisible-ring-engine
  - steinberg-finite-presentation-and-kazhdan-theorem
---

Let `D` be the ring of `finitely-presented-divisible-ring-engine`, with 6 generators and
7 relations. Put `Γ = St_4(D)`, the same group for every `n >= 2`.

1. **Finitely presented.** `D` is a finitely presented unital ring, so `Γ` is finitely
   presented (`steinberg-finite-presentation-and-kazhdan-theorem`, rank 4). By the same
   node it has property (T).
2. **Contains GL_n(Q).** `Q ⊆ D` unitally. Also `x_1 = w`, `y_1 = v`, `x_2 = sw`, `y_2 = vt` form a
   Leavitt pair: `vw = 1`; `vt·sw = v(ts)w = 1`; `sw·vt = s(wv)t = 1 - wv`, so
   `x_1y_1 + x_2y_2 = 1`; and `v·sw = v(1-wv)sw = 0`, `vt·w = vt(1-wv)w = 0`, using
   `sw = (1-wv)sw` and `vt = vt(1-wv)`, which follow from `x_2y_2x_2 = x_2`, `y_2x_2y_2 = y_2`
   (`gq-referee-a` checked this against R1–R3). By `one-steinberg-group-contains-every-gl-n-q`,
   `SL_(4m)(Q)` embeds in `Γ` for every `m`. So does `GL_n(Q) <= SL_(n+1)(Q) <= SL_(4m)(Q)`, via
   `g -> diag(g, det(g)^(-1), 1, ..., 1)` for `4m >= n+1`.
3. **Explicit and natural.** `Γ` is the Steinberg group of a named ring given by an explicit
   finite presentation. It is one group for all `n`, and it is not produced by running an
   embedding algorithm on a presentation of `GL_n(Q)`. The mere existence of a finitely
   presented group containing every `GL_n(Q)` is classical (Higman), and Mikaelian
   (arXiv:2507.04347) announces explicit overgroups for each `n`. So the claim is only
   that this construction is explicit, uniform in `n`, and plausibly natural; experts
   decide naturality.

Compared with `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`: that route uses
`St_(6n+7)(R_L)`, a group that depends on `n`, and a citation-free swindle. This one uses
the one group `St_4(D)` and needs the classical K_2 of matrix rings over `Q`. Either route
reaches the target once its first requirement is refereed.

What this route does not give:
- **Not simple.** `Γ` maps onto `E_4(D)`, whose centre contains `Q^x`
  (`non-ibn-rational-hosts-have-infinite-elementary-centre`). So this does not reach
  `gl-n-q-embeds-in-fp-simple-group`.

Status: the first requirement passed three referees (see its node). `D` itself was reviewed
only by `gq-referee-c`. The companion route `gl-n-q-explicit-via-st-4-of-resolvent-ring`
uses the ring `R_L`, which `gq-referee-b` checked.
