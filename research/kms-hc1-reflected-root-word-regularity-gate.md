---
rg: 2
id: kms-hc1-reflected-root-word-regularity-gate
kind: claim
title: A finite image detects the HC1 root word only if the reflected pair is irregular
---

Let `p` be a prime, `F` a group, and `A,B,C in F` a triple satisfying the
relators of `Gamma_p` from `kms-hc1-reflected-root-word-is-nontrivial`. Put
`R=[B,A]`, `S=[B,C]`, `H=<R,S>` and `w=(RS)^p`. Then:

- **(Lemma)** `R^p=S^p=1`, and `B` commutes with `R` and `S`.
- **(A1)** If `H` is nilpotent of class `<p`, then `w=1`.
- **(A2)** Let `p>=5`. If `[R,S,R]=[R,S,S,R]=[R,S,S,S]=1`, i.e. `(R,S)`
  satisfies the relators of the `B_2` vertex group `Delta_p=<a,c>`, then
  `w=1`.
- **(A3)** If `F` is nilpotent of class `<=2p-1`, then `w=1`.
- **(B)** Let `p>=7` and `F=G(k)` a Chevalley group over a field of
  characteristic `p`. If `A,B,C` are root elements `x_alpha(s)`,
  `x_beta(t)`, `x_gamma(v)` with `s,t,v` nonzero, then `w=1`.
- **(C)** Let `G_0` be a finite `p`-image of `Gamma_p` with kernel `N` in
  which `w` dies, and `M` an `F_l G_0`-module with `l` not equal to `p`. An
  extension `1->M->E->G_0->1` through which `Gamma_p` factors detects `w`
  only if `[w]` is nonzero in `N^ab tensor F_l`. In particular, every
  metabelian image kills `w`.

So for `p>=5`, every finite image that detects `w_p` must have `<R,S>` not a
quotient of `Delta_p`, not nilpotent of class `<p`, and (for `p>=7`) not given by root
elements of a Chevalley group in the defining characteristic. For `p=3`, A3
is sharp: `w_3` survives in the maximal 3-quotient of 3-class 6.

Computed (experiments/kms-coprime-extensions-2026-09-17):

- every 5-group of 5-class `<=12` kills `w_5`;
- every 7-group of 7-class `<=14` kills `w_7`;
- every `p`-image with `[A,C]=1` kills `w_p` (`p=3,5,7`).

Proof: `kms-hc1-reflected-root-word-regularity-gate-proof`.
