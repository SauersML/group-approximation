---
rg: 2
id: bilipschitz-finite-nucleus-rsg-proper-power-germs-are-torsion
kind: claim
title: In a rational similarity group with finite nucleus whose nuclear maps are bi-Lipschitz for a positive edge-weighted metric, an element conjugate to a proper power has finite-order germs at all of its rational periodic points
distinct_from:
  rsg-proper-power-conjugate-germs-torsion-at-finite-orbits: that needs no metric hypothesis but only covers rational periodic points whose orbit under the conjugator is finite; this adds a bi-Lipschitz hypothesis on the nucleus and covers every rational periodic point.
  finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous: that is the open global equicontinuity statement; this is pointwise at rational points and says nothing at irrational points.
---

**ESTABLISHED** (elementary modulo one import; no novelty claimed).

**Setting.**
- `G ≤ R_(Γ,E)` is a rational similarity group (RSG) with finite nucleus, in
  the sense of Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224v3.
- `E` has no isolated points.
- `w` assigns a positive weight to every edge of `Γ`, `w(u)` is the total weight
  of a finite path, `x ∧ y` is the longest common prefix, and
  `d_w(x, y) = exp(-w(x ∧ y))`.
- Every element of `Nuc_G` is `d_w`-bi-Lipschitz on its domain.

**Statement.** Let `f, g ∈ G` and nonzero integers `k, l` with `|k| ≠ |l|`
satisfy `f g^k f^-1 = g^l`. Let `z ∈ E` be a rational point with `g^p z = z`
for some `p ≥ 1`. Then the germ `[g^p]_z` has finite order, so some power of `g`
is the identity on a neighbourhood of `z`.

**What this adds.** `rsg-proper-power-conjugate-germs-torsion-at-finite-orbits`
needs the orbit `{f^n z}` to be finite. Here that orbit may be infinite, which is
exactly where a finite-nucleus host for the Baumslag--Gersten group must put the
attracting dynamics of `a`.

**Scope.**
- **Irrational periodic points:** nothing is said.
- **Equicontinuity:** not given. The missing input is a pumping lemma for nuclear
  maps that are bi-Lipschitz but not similarities. See Attempt 3 of
  `finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous`.
- **Which RSGs satisfy the hypothesis:** not settled.
  - It holds with `w ≡ 1` when nuclear maps are path isometries.
  - The rescaling involution `q` of `research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md`
    §1 is not bi-Lipschitz for `w ≡ 1`, but is for `w(0) = 2`, `w(1) = 1`.
    There its ratios take the values `-1, 0, 1`.
  - Whether the hosts of BBMZ for hyperbolic groups admit such a `w` was not
    checked.

The proof is `bilipschitz-rsg-torsion-germs-proof`.
