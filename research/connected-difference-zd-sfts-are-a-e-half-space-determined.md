---
rg: 2
id: connected-difference-zd-sfts-are-a-e-half-space-determined
kind: claim
title: A Z^d-SFT with coarsely connected difference sets is, in every direction and almost surely for every invariant measure, determined pointwise by all of its half-spaces on one side
distinct_from:
  sft-connected-differences-iff-flexible-sets-stay-close: that is the exact flexibility reformulation and the product criterion; this derives from it an equivariant height function and a measure-zero exceptional set.
  fp-v-times-subshift-full-groups-force-connected-differences: that is the coarse-connectivity necessary condition for finite presentation; combined with it, this becomes a pointwise one-sided determinism necessary condition for P2 hosts over Z^d.
  kari-culik-minimal-subsystem-has-no-expansive-direction: that is about strips determining a configuration (expansive directions); this is about half-spaces, and pointwise on a conull set.
---

**ESTABLISHED.** Route: `connected-difference-zd-sfts-are-a-e-half-space-determined-proof`.

**Setting.** Let `X ⊆ A^(Z^d)` be an SFT whose difference sets are all `m`-connected. Fix a
nonzero `n ∈ R^d`. For `c ∈ R` put `H_c^+ = {p : ⟨p, n⟩ >= c}` and `H_c^- = {p : ⟨p, n⟩ <= c}`.
Say `x ∈ X` is *determined by* a set `U` if every `y ∈ X` with `y|U = x|U` equals `x`.

**Theorem.** `X` is the union of three Borel sets, each invariant under `Z^d`:
- `X_n^+`: points determined by `H_c^+` for every `c`;
- `X_n^-`: points determined by `H_c^-` for every `c`;
- `X_n^0`: points with an equivariant *horizon* `a(x) ∈ R`, where `a(v.x) = a(x) + ⟨v, n⟩`
  for the shift action (up to the sign convention).

`X_n^0` has measure zero for every `Z^d`-invariant Borel probability measure. In particular, for
every ergodic `μ` and every direction `n`, one of `X_n^+` and `X_n^-` has full measure.

**Corollary (for P2 hosts).** If `A(G_V × (Z^d ⋉ X))` is finitely presented, with `X` a free
subshift, then `X` is of finite type
(`fp-v-times-subshift-full-groups-force-quantum-rigidity`). Its difference sets are coarsely
connected (`fp-v-times-subshift-full-groups-force-connected-differences`). So the theorem
applies:
- in every direction `n`, almost every point is determined by each of its half-spaces on one
  fixed side;
- this determination is pointwise, among all points of `X`, and not only modulo null sets.

**What it says about the need on Durand--Romashchenko hosts (board need 8f6fb97d).**
- *Where a kill cannot come from.* The typical hierarchical host is an almost one-to-one
  extension of an equicontinuous factor (odometer, or odometer times rotation), with singleton
  fibres almost everywhere. Its macrotile grid is visible in every half-space. So the a.e.
  statement of the theorem does not obstruct it, and no measure or entropy argument can.
- *Where a kill can come from.* Any failure of coarse connectivity for such a host lives on the
  null set of fault configurations. By part 1 of
  `sft-connected-differences-iff-flexible-sets-stay-close`, it must be a single fault point
  that is flexible on two regions far apart, for example:
  - two opposite quadrants of a fault cross that can be re-chosen independently;
  - the two sides of a thick fault line that can both be re-chosen.
- *Status.* Whether the lift of `minimal-free-z2-sfts-have-arbitrarily-hard-row-languages` has
  such a fault point is not decided here. The data synchronization wires of the lift connect
  the changes they cause, which is weak evidence that it passes.
