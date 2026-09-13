---
rg: 2
id: labbe-full-group-embeds-in-its-supertile-corner
kind: claim
title: Labbé's full group and its derived subgroup are isomorphic to their proper subgroups supported on the supertile anchors
distinct_from:
  labbe-shift-derived-full-group-escapes-known-obstructions: That shows the invariant measure forbids compressing clopen sets inside the group; this records the combinatorial self-similarity that survives, an injective non-surjective endomorphism transporting every relation to the supertile scale.
  labbe-full-group-local-relations-climb: That asks that bounded local relations imply all local relations; this is a tool for it, since relations at the supertile scale are images of relations at the base scale.
artifacts:
  - research/artifacts/fp-simple-relation-climbing-2026-09-13.md
---

**ESTABLISHED.**

**Setting.**
- `Omega_U` is Labbé's shift, `𝒢 = Z^2 ~ Omega_U` its transformation groupoid, and
  `omega = alpha∘beta∘gamma` his self-similar morphism (arXiv:1802.03265, Proposition
  `prop:pre-main`).
- `A = omega(Omega_U)` is the set of tilings whose origin is the bottom-left tile of a level-one
  supertile.

**Statement.**
1. **The anchor set.** `A` is clopen and `0 < mu(A) < 1` for every invariant probability `mu`.
2. **Recoding.** `omega : Omega_U -> A` is a homeomorphism. There is a continuous cocycle
   `L : Omega_U x Z^2 -> Z^2` with `omega(sigma^w x) = sigma^(L(x,w)) omega(x)`, and
   `(x, w) -> (omega(x), L(x, w))` is an isomorphism of `𝒢` onto the reduction `𝒢|_A`.
3. **The endomorphism.** Put `Phi(g)(omega(x)) = omega(g(x))` on `A` and `Phi(g) = id` off `A`.
   Then `Phi : [[𝒢]] -> [[𝒢]]` is an injective homomorphism whose image is
   `{h ∈ [[𝒢]] : h = id on Omega_U \ A}`.
4. **The derived subgroup.** `Phi` maps `D([[𝒢]])` isomorphically onto the derived subgroup
   `D_A` of that image. `D_A` is a proper subgroup of `D([[𝒢]])`, since it fixes the nonempty
   clopen set `Omega_U \ A` pointwise.

**Consequences for relations.**
- `D([[Z^2 ~ Omega_U]])` is not co-Hopfian.
- For every relation `w(s_1, ..., s_n) = 1` among generators, `w(Phi(s_1), ..., Phi(s_n)) = 1`
  is a relation among 3-cycles on supertile multisections.
- So relations at the supertile scale are `Phi`-images of relations at the base scale. What
  `labbe-full-group-local-relations-climb` still needs is to express the `Phi(s_i)` through
  bounded local relations, not to rederive each scale from the previous one.
- No invariant-measure compression is involved. `Phi` is not inner, because `mu(A) < 1`.

No novelty is claimed beyond the formulation. Recoding a self-similar hull onto its supertile
anchors is standard; the point here is the resulting corner endomorphism of the full group.

**Proof:** `labbe-full-group-embeds-in-its-supertile-corner-proof`.
