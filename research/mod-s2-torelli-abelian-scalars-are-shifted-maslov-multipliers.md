---
rg: 2
id: mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers
kind: claim
title: Honest Mod(S_2) representations with abelian Torelli image put a separating twist near a scalar exactly when a finite-index subgroup of Sp4(Z) realizes the shifted Maslov multiplier plus a small Torelli transgression class
distinct_from:
  mod-s2-real-untwisting-identifies-deligne-norm-parameters: that transports point-norm asymptotic models between Sp4(Z) and Mod(S_2) at one global parameter; this decomposes honest representations of Mod(S_2) with abelian Torelli image into Torelli eigencharacter orbits and reads each orbit as an exact projective representation of a finite-index subgroup with a non-constant (small) parameter.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the operator-norm gap for all honest representations; this is an exact equivalence for the Torelli-abelian ones, which turns the gap on that class into an arithmetic statement about finite-index subgroups.
  mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors: that bounds finite-image models level by level through normalized-HS character limits; this is an exact dictionary for every Torelli-abelian honest representation, finite image or not.
  deligne-sector-determinants-see-only-dimension-mod-three: that kills determinant and trace-log invariants; this keeps the full eigencharacter data of the Torelli action.
---

**ESTABLISHED** through `mod-s2-torelli-abelian-scalars-shifted-multipliers-proof`. Unreviewed; no novelty claimed.

**Setting.** As in `mod-s2-real-untwisting-identifies-deligne-norm-parameters`: `M = Mod(S_2)`,
`pi : M -> Gamma = Sp_4(Z)`, `K = ker pi`, `b` the normalized integral universal-cover cocycle of `Gamma`,
`f : M -> R` the unique real untwisting (`df = b o pi`, `f|_K = r sigma`, `r = a/10`, `3` not dividing `a`).

- `X` is the set of symplectic splittings of `H_1(S_2;Z)`; `Gamma` acts on it transitively.
- `A = K/[K,K]`. By Mess's theorem (`genus-two-torelli-freely-generated-by-separating-twists`) it is the
  free abelian group on `{[t_x] : x in X}`, and `M` acts on it through `Gamma` by permuting `X`.
- `G = M/[K,K]`, fix a section `s : Gamma -> G` with `s(e) = e`, and let
  `a(g,g') = s(g)s(g')s(gg')^-1 in A`.
- For a finite-index `Gamma' <= Gamma` and a `Gamma'`-invariant bounded `h : X -> R`, extend `h`
  linearly to `A` and put `Phi_(Gamma')(h) := [h o a] in H^2(Gamma'; R)`. This is a real 2-cocycle
  because `h` is `Gamma'`-equivariant into the trivial module; its class does not depend on `s`.
- A class `gamma in H^2(Gamma';R)` is **fd-realizable** if the class `exp(2 pi i gamma)` in `H^2(Gamma';T)`
  is the multiplier of an exact projective unitary representation `Gamma' -> U(m)`, `m < infinity`.
- An honest representation `rho : M -> U(d)` is **Torelli-abelian** if `rho(K)` is abelian, that is,
  `rho` factors through `G`.

**Statement.** For `alpha in R/Z` and `lambda = exp(2 pi i alpha)` the following are equivalent.

1. **(TA1)** For every `epsilon > 0` there is a Torelli-abelian honest `rho` with
   `||rho(t_s) - lambda I||_op < epsilon`.
2. **(TA2)** For every `eta > 0` there are a finite-index `Gamma' <= Gamma` and a `Gamma'`-invariant
   `h : X -> [-eta, eta]` such that
   ```text
   Phi_(Gamma')(h) - (alpha / r) [b|_(Gamma')]      is fd-realizable on Gamma'.
   ```

Quantitatively: from `rho` with `||rho(t_s) - lambda I|| <= epsilon < 2` one gets (TA2) with `eta = epsilon/4`,
`Gamma'` the stabilizer of one Torelli eigencharacter of `rho`, and realizing dimension at most `dim rho`.
Conversely (TA2) at `eta` gives `rho` with `||rho(t_s) - lambda I|| <= 2 pi eta`, of dimension
`[Gamma : Gamma'] m`.

**Consequences.**
- Put `Z_ab = { alpha : (TA1) holds }`. Then `Z_ab <= Z_hon <= Z_op`, with `Z_hon` as in
  `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`. So **if (TA2) holds at `alpha = 1/3`,
  the gap node fails and with it `deligne-triple-cover-exact-mf-radical`** (via (U4) of the untwisting node).
- The Torelli-abelian part of the operator-norm gap is therefore exactly the arithmetic statement
  `sp4-shifted-maslov-multipliers-stay-far-on-finite-index`.
- At `h = 0`, `Gamma' = Gamma` the class is `-(alpha/r) b`, and (TA2) reduces to exact realizability of a
  Maslov multiplier: the point where Deligne's theorem acts. The new freedom is twofold: pass to finite index,
  and move the parameter by a small **non-constant** Torelli function `h`, whose class `Phi(h)` may point in
  directions of `H^2(Gamma';R)` that do not come from `Gamma`.
