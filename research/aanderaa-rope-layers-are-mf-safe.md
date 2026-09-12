---
rg: 2
id: aanderaa-rope-layers-are-mf-safe
kind: claim
title: The three Aanderaa rope layers preserve MF over an MF Boone engine and residually finite input
distinct_from:
  mf-safe-asymmetric-hnn-replacement: that is the rope edge of Rotman's benign-witness compiler; this concerns the three stable letters of Aanderaa's compiler, whose edge groups are free.
  boone-group-is-mf: that is the engine; this is the rope on top of it.
---

Let `Gamma` be a finitely generated recursively presented group whose
relators are enumerated by `T`, and form (Marchand's notes, after Rotman
12.18 / Aanderaa)

```text
G_4 = G_nb(T) * Gamma,
G_5 = < G_4, tau_j | [tau_j, s_k] = [tau_j, s'_k] = 1, tau_j^-1 k_0 tau_j = k_0 s'_j^-1 >,
G_6 = < G_5, d | [d, k_0] = 1, d^-1 s_j tau_j d = s_j >,
G_7 = < G_6, sigma | [sigma, k_0] = [sigma, s_j] = 1, sigma^-1 t_0 sigma = t_0 d >.
```

`G_7` is finitely presented and contains `Gamma`.  Show that `G_7` is MF
whenever `G_nb(T)` is MF and `Gamma` is residually finite (the `INF` value
`B2(1)` of [[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]).

## Attempts

*Layer `tau_j`.*  The associated subgroups coincide: `U = <s_k, s'_k, k_0>
= F(A cup {k_0}) * Gamma`, and the twist is the automorphism of `U` fixing
`A` and `Gamma` and sending `k_0` to `k_0 s'_j^-1`.  It does not extend to an
automorphism of `G_4` (it would have to move `k` against the relations `[k,
r_i] = 1`), so the inner-envelope lemma needs an envelope for `U` inside
`G_4`, not for `G_4` itself; `G_5 = G_4 *_U (U x| F_J)` is an amalgam over
`U` of `G_4` with a mapping torus of a free product by free-group
automorphisms.

*Layers `d` and `sigma`.*  Both have free edge groups in this setting
(`<k_0, s_j tau_j>` to `<k_0, s_j>`, and `<k_0, s_j, t_0>` to `<k_0, s_j, t_0
d>`), so each is an HNN extension by an isomorphism of free subgroups; the
twisted-edge theorem or an envelope is needed for each.

No layer has been closed; the value of the decomposition is that each edge
is explicit and free, unlike the product-twist edge of the benign-witness
rope.
