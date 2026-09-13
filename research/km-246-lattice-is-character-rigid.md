---
rg: 2
id: km-246-lattice-is-character-rigid
kind: claim
title: For q >= 4 the (2,4,6) Kac-Moody lattice S_q is character rigid, with only the regular and trivial extreme characters
distinct_from:
  caprace-thom-v2-leaves-km-character-rigidity-open: that records that Caprace--Thom v2 does not prove character rigidity of these lattices; this proves it at type (2,4,6), q >= 4, by a route that avoids square-integrability.
  km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4: that is IRS rigidity, which classifies only fixed-point characters; this classifies all characters, using IRS rigidity as one input.
  character-rigid-fp-simple-groups-stability-dictionary: that is the stability dictionary for any character-rigid finitely presented infinite simple group; this supplies the Kac--Moody member of that class.
---

**ESTABLISHED (unreviewed).** Let `q >= 4` be a prime power and `S_q = Λ_q/Z` the
`(2,4,6)` Kac--Moody lattice of `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`.

```text
(CR1) If π: S_q -> U(M) is a representation into a finite factor with π(S_q)'' = M, then
      either π extends to an isomorphism L(S_q) -> M, or M = C and π is trivial.
(CR2) Every extreme normalized character of S_q is δ_e or 1. Every normalized character is
      t δ_e + (1-t) 1 for some t in [0,1].
(CR3) The full C*-algebra C*(S_q) has exactly two extreme tracial states.
```

**Why it matters.**
- With `character-rigid-fp-simple-groups-stability-dictionary`, `S_q` is hyperlinear iff it
  is not HS-stable, and sofic iff it is not permutation stable
  (`km-246-lattice-stability-dictionary`). So hyperlinearity of the finitely presented simple
  Kazhdan group `S_q` is decided by whether one asymptotic representation fails to collapse
  on one element.
- (CR1) is operator-algebraic superrigidity in Connes' sense, as in the introduction of
  Creutz--Peterson, for a finitely presented simple Kazhdan group that is not linear.

**Credit and history.**
- Caprace--Thom arXiv:2606.27993v1 announced (CR2) as its "Theorem D". It deduced
  square-integrability of `Λ_+ < L_+` from Rémy's integrability theorem.
- v2 withdrew it (Remark 5.4): that theorem concerns `S_q < L_+ x L_-`, not `Λ_+ < L_+`, and
  in the hyperbolic case `Λ_+` is distorted.
- The proof here never uses square-integrability. It runs Creutz--Peterson's argument for
  their Theorem 6.3 with Proposition 4.1(ii) replaced by
  `irs-rigid-simple-dense-subgroups-act-properly-outer`, whose inputs are Caprace--Thom v2's
  own IRS rigidity (Corollary 5.3) and the simplicity of `S_q`.
- No priority is claimed for the statement. The substitution has not had independent review.

**Scope.** The same argument should cover any compact hyperbolic type for which Caprace--Thom's
Proposition 4.1 gives (T) and `Λ/Z` is simple. That is not claimed here.

Proof: `km-246-character-rigidity-via-irs-substitution`.
