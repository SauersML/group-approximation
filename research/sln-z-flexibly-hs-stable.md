---
rg: 2
id: sln-z-flexibly-hs-stable
kind: claim
title: SL_n(Z) for some n at least three is flexibly Hilbert-Schmidt stable
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - research/artifacts/low-energy-schreier-frame-construction-2026-09-05.md
  - research/artifacts/second-moment-schreier-positive-corner-2026-09-05.md
  - research/artifacts/positive-canonical-corners-bootstrap-stability-2026-09-05.md
  - research/artifacts/soft-schreier-mass-positive-corner-2026-09-05.md
  - research/artifacts/spectral-pair-products-control-schreier-gram-2026-09-05.md
  - research/artifacts/flexible-correction-forces-universal-schreier-mass-2026-09-05.md
  - research/artifacts/universal-host-captures-all-low-energy-types-2026-09-05.md
  - research/artifacts/expansion-blocks-local-schreier-spectral-seeds-2026-09-05.md
  - research/artifacts/maximal-canonical-residual-has-uniform-spectral-exclusion-2026-09-05.md
distinct_from:
  sl2-z-inverse-pq-is-hs-stable: that is stability of the three-place S-arithmetic lattice SL_2(Z[1/pq]); this is stability of the plain higher-rank lattice SL_n(Z), a (T) group.
  iwahori-local-global-defect-question: that is (equivalent to) flexible stability of SL_2(Z[1/2]); this is the plain SL_n(Z), covered by neither Dogon nor Dogon-Vigdorovich.
---

Decide whether `SL_n(Z)` (`n >= 3`) is flexibly Hilbert--Schmidt stable
(Dogon--Vigdorovich Def 1.2 / Becker--Lubotzky flexible stability): every
asymptotic unitary representation is, after padding by a vanishing-density
corner, generatorwise close in normalized HS norm to a genuine
finite-dimensional representation. For a finitely generated group this
also gives pointwise closeness on every fixed group element; no supremum
over all elements is part of this definition.

By `sln-z-thin-codense-tau-pair` and
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, a positive answer
produces an explicit non-hyperlinear group
`G = <SL_n(Z), t | [t, C] = 1>` (`C` a thin co-dense subgroup).

## Attempts

- **Universal spectral host and residual exclusion (2026-09-05).**
  `(MSC16)` proves that Q_(2d) captures every possible low-energy type
  from every finite quotient whenever `2h epsilon^2/kappa^2<=1/2`.
  Counts and unnormalized source Gram matrices dominate those of every
  other host. Thus no search over larger quotients remains. A maximal
  residual of a hypothetical unstable canonical sequence has vanishing
  normalized count uniformly over all finite hosts as the cutoff tends
  to zero. The index-free perturbation bound `(MSC18)` preserves this
  exclusion under o(1) HS changes, including QRC. Constructing local
  word-halo trials cannot close the gap: `(MSC17)` forces low-energy
  maps to occupy almost all cosets, even in exact examples; a local
  polynomial filter needs degree at least logarithmic in the quotient
  index. The remaining task is a global count argument at the fixed
  universal host, or another contradiction for the residual. No fixed
  positive spectral gap is claimed.
- **Source Gram control is automatic; spectral count remains
  (2026-09-05).** `(MSC14)` uses pair-product conjugation and a positive
  weighted spectral trace to prove
  `r<=Tr(B^2)<=r/(1-2h epsilon^2/kappa^2)` for the full low-energy
  space of dimension r. Thus r/d bounded below supplies every Gram
  condition used below. More directly, its irreducible blocks form an
  exact representation of dimension r; polar completion gives an exact
  rank-r corner with error linear in epsilon, or a padded full correction
  when r>d. Exact multiplicity embeddings give deterministic sublinear
  seeds along canonical sequences of positive count. Conversely,
  `(MSC15)` shows that any known flexible correction forces r/d to one
  at suitable cutoffs in the fixed universal host Q_(2d). The remaining
  existence question is whether every canonical sequence admits a
  subsequence and quotient/cutoff choices with positive normalized
  low-energy count. The nonuniform corner bootstrap makes this sufficient
  for full stability. Arbitrarily small cutoffs can miss almost all of
  an already correctable tuple, so the choice still needs proof.
- **Positive soft spectral mass suffices (2026-09-05).** The moment
  hypothesis below can be replaced by
  `tr[H(H+I)^(-1)]>=c>0`, with c depending on the canonical sequence.
  `(MSC13)` uses a globally contractive soft polar frame and a spectral
  coarea estimate to recover at least a c/2 fraction of the input. Its
  direct isometric correction has an explicit vanishing error bound;
  sublinear trivial seeds are also available with qualitative vanishing
  error. The same nonuniform positive-corner bootstrap would establish
  full stability. Choosing quotient hosts and cutoffs tending to zero
  with this positive mass is still unproved. Neither existence of a
  nonzero low-energy vector nor a small curvature support provides a
  positive lower bound for the normalized mass.
- **Bounded spectral Gram moments suffice (2026-09-05).** For SL5,
  `(MSC10)--(MSC12)` in
  `moving-subgroup-schreier-correction-has-no-index-loss` construct small
  Schreier frames from low-energy rectangular intertwiner spaces. The
  target covariance needed to compress the frame is automatically
  sublinear for canonical inputs whenever the spectral-space dimension
  is bounded below relative to the input dimension. If the normalized
  source Gram matrix H has `tr(H^2)<=M`, a spectral band supplies a
  correctable canonical corner of relative dimension at least `1/(16M)`.
  Such positive-corner recovery for every canonical sequence, even only
  on a subsequence and with sequence-dependent M, bootstraps to full
  flexible stability by maximal recoverable mass and constant-one ucp
  untensoring. The unresolved input is the existence of quotient hosts
  and cutoffs tending to zero with this bounded second moment. Small
  curvature has not supplied it. An arbitrarily tiny cutoff can miss
  half of an already correctable tuple, so the cutoff cannot be chosen
  without a coverage or moment argument.
- **Not ruled out by the (T) obstruction.**  `SL_n(Z)` is an infinite
  hyperlinear Kazhdan group, so it is not STRICT/local HS-stable
  (`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`), but that says
  nothing about FLEXIBLE stability, which is the entire open subject of
  Dogon arXiv:2211.10492.
- **Not ruled out by cohomological obstructions.**  Ioana--Spaas--Wiersma
  (arXiv:2006.01874) LLP/LP obstructions do not reach `SL_n(Z)`; the relevant
  central extensions are finite (`K_2(Z) = Z/2`), and finite extensions of
  hyperlinear groups are hyperlinear, so no ISW-type instability is known.
- **Genuinely open, like every host.**  No infinite (T) group is known to be
  flexibly HS-stable or weakly ucp-stable; this is the shared open core
  (see the [archived conditional-route survey](artifacts/nonhyperlinear-conditional-routes-landscape.md)).  The sharpest published
  toolkit toward it is de la Salle arXiv:2204.07084 (finite-group
  exactification with linear dimension-free constants in an arbitrary tracial
  target) plus a length-control estimate for the congruence relator family.
