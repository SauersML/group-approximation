---
rg: 2
id: surface-torelli-groups-fp-for-large-genus
kind: claim
title: "There is g_0 such that the Torelli group of the closed genus g surface is finitely presented for every g >= g_0"
---

Let `I_g = ker(Mod(S_g) -> Sp_{2g}(Z))` for the closed oriented surface `S_g`. The
claim: there is `g_0` such that `I_g` is finitely presented for every `g >= g_0`.
It is the yes-answer for the surface family of Zaremsky Problem 3.1
(`zaremsky-3-01-surface-torelli-resolved`). The same statement with one marked
point or one boundary component is equivalent
(`surface-torelli-fp-invariant-under-puncture-and-boundary`).

Known: `I_g` is finitely generated for `g >= 3` (Johnson). Kassabov–Putman (Math.
Ann. 376 (2020), §1): "it is not known whether `I_g^b` is finitely presentable for
`g >= 3`."

## Attempts

- **Degree 2 obstruction, now removed.** Finite presentability requires
  `H_2(I_g; Z)` to be finitely generated. That was open as of Kassabov–Putman
  (2020), who proved finite generation as a `Z[Sp_{2g}(Z)]`-module for `g >= 3`
  (their Theorem A). It is now known integrally for `g >= 4`: Gaifullin,
  arXiv:2606.13517 (June 2026, preprint), Theorem A gives `H_k(I^b_{g,p}; Z)`
  finitely generated for `k <= g - 2` and `b + p <= 1`. Rationally,
  `H_2(I^b_{g,p}; Q)` is finite dimensional for `g >= 5` (Minahan–Putman,
  arXiv:2504.00211, Theorem B). Status: necessary conditions hold for `g >= 4`;
  not sufficient.
- **Brown's criterion on the complex of cycles.** Bestvina–Bux–Margalit
  (arXiv:0709.0287) build a contractible complex of cycles on which `I_g` acts;
  it gives `cd(I_g) = 3g - 5`. For a presentation, Brown's criterion needs finitely
  many orbits of low-dimensional cells and finitely presented stabilizers. `I_g`
  has infinitely many orbits because it has infinite index in `Mod(S_g)`. In
  genus 3, Gaifullin (arXiv:2011.00295) shows the `E^3_{0,2}` term of the
  associated spectral sequence is infinitely generated. Where it dies: infinitely
  many orbits and non-finitely-presented stabilizers.
- **Finite equivariant presentations.** Kassabov–Putman (Definition 1.2) introduce
  finite `Γ`-equivariant presentations, where the generators and relators are finite
  modulo a group `Γ` acting on `G`, here `Γ = Mod(S_g)` acting by conjugation. Such a
  presentation gives module-finiteness of `H_2`. Where it dies: the orbit sets are
  infinite, and no mechanism is known that makes a finite subset of relators suffice.
- **Surface partial Torelli groups.** Ershov (arXiv:2601.01377, introduction)
  records that finite presentability of the partial Torelli groups `I_{g,b;d}` is
  open apart from `d = 0`. His Aut(F_n) peak-reduction method has no surface
  analogue in the literature found.
