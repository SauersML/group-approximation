---
rg: 2
id: ascending-unions-embed-along-coherent-chains
kind: claim
title: An ascending union embeds in a group exactly when its terms embed along a chain whose restrictions agree up to conjugacy
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that compares the targets for different n; this is a general criterion for one ascending union in one host.
  gl-n-q-embeds-in-fp-simple-group: that is the open problem; this rephrases it as a coherence condition on the chain GL_n(Z[1/m!]) inside one finitely presented simple group.
---

**ESTABLISHED** through `ascending-unions-embed-along-coherent-chains-proof`. Not
independently reviewed. This is folklore and no priority is claimed.

## Statement

Let `H_1 <= H_2 <= ...` be groups with union `H`, and let `Gamma` be a group. The
following are equivalent.

1. `H` embeds in `Gamma`.
2. **Extension form.** There are injective homomorphisms `iota_m : H_m -> Gamma`
   with `iota_(m+1)|H_m = iota_m` for all `m`.
3. **Conjugacy form.** There are injective homomorphisms `iota_m : H_m -> Gamma`
   and elements `g_m in Gamma` with `iota_(m+1)|H_m = c(g_m) o iota_m`, where
   `c(g)` is conjugation by `g`.

**Class form (sufficient).** For each `m` let `C_m` be a nonempty set of
embeddings `H_m -> Gamma` that forms a single `Gamma`-conjugacy class. Suppose some
member of each `C_(m+1)` restricts to a member of `C_m`. Then 3 holds, so `H`
embeds in `Gamma`.

## Instances

- **Belk--Hyde--Matucci, `Q <= T-bar` (arXiv:2005.02036, Lemma 7).** Here
  `H_m = (1/m!)Z` and `Gamma = T-bar`. Put `iota_m(1/m!) = s_m`, where `s_1 = z` is
  the central translation and `s_m^m = s_(m-1)`. Lemma 7 supplies the next root
  inside `T-bar`. This is the extension form.
- **P. Hall's universal locally finite group.** Isomorphic finite subgroups are
  conjugate there, so the class form applies to every chain of finite groups.
- **The root `gl-n-q-embeds-in-fp-simple-group`.** `GL_n(Q)` is the union of the
  groups `GL_n(Z[1/m!])`, since the entries of a matrix and of its inverse have
  bounded denominators. So `GL_n(Q)` embeds in a finitely presented simple group
  `Gamma` if and only if `Gamma` contains the whole chain `GL_n(Z[1/m!])`, with
  embeddings that agree up to conjugacy on restriction.
  - Each `GL_n(Z[1/m!])` separately has such a host (Zaremsky arXiv:2405.09722,
    Theorem 1.2), but those hosts depend on `m`.
  - The criterion isolates the two missing ingredients: one host for all `m`, and
    enough conjugacy rigidity of the chosen embeddings.
