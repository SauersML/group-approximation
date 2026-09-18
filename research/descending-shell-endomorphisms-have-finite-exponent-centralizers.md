---
rg: 2
id: descending-shell-endomorphisms-have-finite-exponent-centralizers
kind: claim
title: A descending window-zero shell endomorphism of an FW group has a centralizer of finite exponent, so corner and transplant endomorphisms never give one
distinct_from:
  fw-shell-inputs-at-window-zero-are-highly-transitive: that shows the descending relation forces high transitivity on finitely many cofinite orbits and a trivial centre; this uses that to bound the centralizer of the image of the endomorphism, which that node does not treat.
  fw-window-zero-descending-sign-forces-trivial-core: that forces the endomorphism core to be trivial; this is a second, independent necessary condition on the endomorphism.
  binary-leavitt-elementary-groups-have-trivial-core-endomorphisms: that exhibits the corner endomorphism with trivial core; this shows no genuine action realizes it.
requires:
  - fw-shell-inputs-at-window-zero-are-highly-transitive
  - fw-window-zero-descending-sign-forces-trivial-core
  - binary-leavitt-elementary-groups-have-trivial-core-endomorphisms
---

**ESTABLISHED** by `descending-shell-centralizer-proof` (lane proof, elementary, not
independently reviewed; no novelty claimed).

## Statement

Let `P` have property FW, `ρ : P -> Sym(N)` an action in which every `ρ_g`, `g != 1`, has
infinite support, and `ψ : P -> P` an endomorphism with

    s ρ_g s^-1 = ρ_(ψ(g))   in NearSym(N), for every g in P.                 (D1)

1. **Finite exponent.** The centralizer `C_P(ψ(P))` has finite exponent: there is `p >= 1`
   (the number of infinite `P`-orbits) with `c^(p!) = 1` for every `c` in it.
2. **No large commuting subgroups.** `C_P(ψ(P))` contains no nontrivial subgroup without a
   proper subgroup of finite index. In particular it contains no conjugate of `ψ(P)` when `P`
   is infinite and simple.
3. **Corner and transplant endomorphisms are excluded.** For `P = EL_n(L_(F_2)(1,2))`,
   `n >= 3`, and the corner endomorphism `F(g) = I + s_1 (g - I) t_1`, no action as above
   satisfies (D1) with `ψ = F`. The unit `u = s_2 t_1 + s_1 t_2` conjugates `F` to
   `F'(g) = I + s_2 (g - I) t_2`, whose image commutes with `F(P)` and is isomorphic to `P`.

The same argument excludes every endomorphism that transplants a group of homeomorphisms
into a proper clopen set `U` whenever some element moves `U` off itself, for example the cone
transplants of Thompson-like groups; those groups are not FW, so this is recorded only as the
shape of the obstruction.

## Consequence

A descending window-zero shell for an FW input needs an endomorphism whose image has
centralizer of finite exponent, in addition to trivial core. The corner endomorphism of
`binary-leavitt-elementary-groups-have-trivial-core-endomorphisms` meets the second condition
and fails the first. No FW input with an endomorphism meeting both conditions is known.
