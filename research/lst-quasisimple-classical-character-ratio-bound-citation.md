---
rg: 2
id: lst-quasisimple-classical-character-ratio-bound-citation
kind: route
title: Larsen–Shalev–Tiep Theorem 1.2.1 and Definition 4.1.1, read from the Annals PDF
target: lst-quasisimple-classical-character-ratio-bound
requires: []
artifacts: [research/artifacts/sk-fp-sofic-c-unitary-gap-2026-09-13.md]
---

# Literature import (not a new theorem)

**Source.** Michael Larsen, Aner Shalev, Pham Huu Tiep, *The Waring problem for finite simple groups*, Ann. of Math. (2)
**174** (2011), 1885–1950, doi:10.4007/annals.2011.174.3.10. I read the publisher PDF
(https://annals.math.princeton.edu/wp-content/uploads/annals-v174-n3-p10-p.pdf), pages 1889 and 1907, as page images.

**Theorem 1.2.1 (p. 1889), verbatim.** "If Γ is a finite quasi-simple classical group over F_q and g ∈ Γ is an element of
support at least N, then |χ(g)|/χ(1) < q^{−√N/481} for all 1_Γ ≠ χ ∈ Irr(Γ)." The next sentence reads: "See Theorem 4.3.6
for more precise bounds."

**Definition 4.1.1 (p. 1907), verbatim.** "The support supp(g) of an element g ∈ GL_n(F) ⊂ GL_n(F̄) is the codimension of the
largest eigenspace of g: supp(g) = inf_{λ∈F̄} codim ker(g − λ). The support of any element in a classical group G(F) is the
support of its image under the natural representation ρ: G(F̄) → GL_n(F̄)."

**Assembly.**
- A noncentral element of a finite quasi-simple classical group has support at least 1. The argument is on the claim node:
  a support-0 element maps to a scalar, and the kernel of ρ is central.
- Taking `N = 1` gives `(LST1)`.
- `q^{-1/481} <= 2^{-1/481}` for every prime power `q`.

**Also on p. 1907, recorded and not imported.** LST quote Gluck [Glu95]: if G is a finite connected reductive group over F_q
whose commutator subgroup is quasi-simple and simply connected, g ∈ G is noncentral and χ is a nontrivial irreducible
character, then |χ(g)|/χ(1) ≤ γ_q, where γ_q = 19/20 for 2 ≤ q < 43 and γ_q = 1/(√q − 1) for q ≥ 43.
- Read literally, this fails for nontrivial linear characters of `GL_n(q)` at noncentral elements of `SL_n(q)`. So only its
  quasi-simple case is meaningful as quoted.
- Gluck's primary paper was not opened.
- Exceptional groups of bounded rank would need that primary source.
