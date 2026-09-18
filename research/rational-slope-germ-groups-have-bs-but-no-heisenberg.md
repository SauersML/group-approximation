---
rg: 2
id: rational-slope-germ-groups-have-bs-but-no-heisenberg
kind: claim
title: Germs with rational asymptotic slope contain every BS(1,m) but no nonabelian nilpotent group
distinct_from:
  va-singular-point-germ-groups-are-t-bar: that is the slope-one germ group T-bar that VA actually has, which has no distortion; this is the larger germ group allowing rational asymptotic slopes, which has exponential distortion.
  aff-q-does-not-embed-in-aut-thompson-f: that excludes Aff(Q) and U_3(Q) from T-bar and Aut(F); this is a germ group outside VA where BS(1,m) does live, and it shows Heisenberg groups still cannot.
  gl-n-q-embeds-in-fp-simple-group: that is the open target; this constrains which germ groups a Belk–Hyde–Matucci-type host for it must use.
artifacts:
  - research/artifacts/gq-gq-q-in-germs-anatomy.md
---

**ESTABLISHED** through `rational-slope-germ-groups-have-bs-but-no-heisenberg-proof`.
Lane proof; not independently reviewed. No priority is claimed.

**Definition.** `PL₂(R)` is the group of increasing PL homeomorphisms of `R`
- with pieces `x ↦ 2^n x + d` (`n ∈ Z`, `d` dyadic),
- with dyadic breakpoints, finitely many on each compact interval.

Let `z(y) = y + 1`. Let `E` be the group of germs at `+∞` of elements `φ ∈ PL₂(R)` such
that `φ(y + q) = φ(y) + r` for all large `y`, for some integers `q, r ≥ 1`.
- The value `λ(φ) = r/q` is the asymptotic slope.
- Through the map `h` of `va-singular-point-germ-groups-are-t-bar-proof` (`+∞` of `R`
  corresponds to `0̄` after the flip `y ↦ −y`), `E` is the group of germs at `0̄` of
  order-preserving homeomorphisms that are locally in `V` off `0̄` and satisfy
  `φ∘L^q = L^r∘φ`.
- The germ group `G_{0̄} ≅ T̄` of `VA` is the subgroup `q = r = 1`.

**Statement.**
1. `E` is a group and `λ: E → Q_{>0}` is a surjective homomorphism. Its kernel `K` is
   the directed union over `q ≥ 1` of the germ groups of the centralizers `C(z^q)` in
   `PL₂(R)`. Each `C(z^q)` is isomorphic to `T̄`. `E` is torsion-free.
2. For every `m ≥ 2`, `E` contains `BS(1,m) = ⟨a, b | a b a^-1 = b^m⟩` as
   `⟨δ_m, z⟩` with `λ(δ_m) = m`. In particular `z` is exponentially distorted in a
   finitely generated subgroup of `E`, unlike in `VA` (O4).
3. Every nilpotent subgroup of `E` is abelian. In particular no Heisenberg group
   `U_3(Z)` embeds in `E`.

**Meaning for the targets.**
- **Aff(Q).** A finite germ extension of `V` whose singular germs lie in groups like
  `E` is not excluded by O4.
- **Heisenberg.** No such germ group can carry a Heisenberg group. `U_3(Z) ≤ SL_3(Z)`
  already has a distorted centre. So for `U_3(Q)`, and for `GL_n(Q)` with `n ≥ 3`, the
  distortion has to come from germs of a different kind, for example the
  two-dimensional germs of Brin–Thompson groups `nV`, or from non-germ sources.
- **Scope.** This is a germ-level statement. Whether a global group whose singular germs
  lie in `E` can contain `U_3(Z)` through its `V`-part is not decided here.

The open follow-up for `Aff(Q)` is `rational-slope-germ-group-contains-aff-plus-q`.
