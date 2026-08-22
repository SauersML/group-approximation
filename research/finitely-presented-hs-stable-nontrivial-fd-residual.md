---
rg: 2
id: finitely-presented-hs-stable-nontrivial-fd-residual
kind: claim
title: Exhibit a finitely presented uniformly HS-stable group with nontrivial finite-dimensional residual
artifacts:
  - research/artifacts/published-nonhyperlinear-shortcut-audit-2026-08-21.md
distinct_from:
  leavitt-steinberg-hs-stable: that asks only for stability of the binary Leavitt Steinberg group, whose finite-dimensional invisibility data must still be matched to a nontrivial abstract word.
  literal-mark-quotient-not-stable-in-finite-actions: that proves instability for permutation/Hamming models of a specific sofic quotient rather than normalized-HS stability.
---

OPEN.  Produce a finitely presented group `Gamma` and a word `w` satisfying

```text
w!=1 in Gamma,
pi(w)=I for every finite-dimensional unitary representation pi,
Gamma is uniformly flexibly stable in normalized Hilbert--Schmidt norm.
```

By `hs-stability-plus-fd-residual-forces-nonhyperlinearity`, this is a direct
nonhyperlinear witness.  It is enough that `w` be nontrivial in the ordinary
finite residual.  The analytic condition is the hard part: fixed-rank or
Fredholm-index defects dilute like `sqrt(r/d)`, and property `(T)` or
Frobenius stability alone does not supply dimension-free normalized-HS
stability.

## Attempts

- The minimally almost periodic criterion is the special case recorded by
  `map-matricial-stability-non-mf`; it demands much more finite-dimensional
  invisibility than is needed here.
- The binary Leavitt Steinberg candidate has strong finite-dimensional
  collapse data, but `leavitt-steinberg-hs-stable` remains open.
- A nontrivial finite residual is algebraically convenient, but the known
  non-residually-finite telescope examples are not thereby HS-stable.
- **Primary-source audit, 2026-08-21.**  The new polynomially stable
  lamplighter group (Dogon--Vidick, arXiv:2607.20135) is residually finite and
  not finitely presented; the new chordal graph-product examples (Spaas,
  arXiv:2603.02058) are residually finite in the finitely generated cases.
  Published non-residually-finite examples in arXiv:2307.13155 are explicitly
  only *locally* HS-stable and not HS-stable.  No checked example meets all
  three requirements of this claim.
- Exact invisibility cannot fill the analytic gap:
  `exact-fd-invisibility-has-no-general-hs-robustification` gives a finitely
  presented sofic counterexample.
- Local stability does not enlarge the finitely presented search.
  `finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear` imports
  Fournier-Facio--Gerasimova--Spaas Lemma 3.11: local and global HS stability
  coincide for finitely presented groups, including flexible variants.
  Hence their non-RF locally stable but globally unstable examples are
  necessarily infinitely presented.  Finding a finite presentation with
  the same local property would already solve this node rather than provide
  an intermediate theorem.
