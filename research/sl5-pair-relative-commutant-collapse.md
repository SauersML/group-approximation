---
rg: 2
id: sl5-pair-relative-commutant-collapse
kind: claim
title: The rank-four pair carries the whole collapse lane and is the only instance with degree-two cohomology infrastructure
distinct_from:
  sl3-pair-relative-commutant-route: that is the n = 3 instance, chosen for property (T) of the subgroup; this is the n = 5 instance, which keeps every established lane theorem verbatim (trivial center, odd n, rank >= 2) and additionally has Bader-Sauer property (T_2) and (T_3) -- degree-2 unitary cohomology vanishing infrastructure that n = 3 PROVABLY lacks (non-vanishing at degree N-1 for N in {3,4}).
  relative-commutant-collapse-for-sl2-pair: that is the rank-one pair where the subgroup is only Haagerup and the Weyl system degenerates to one involution; this is the deepest-rank instance, where every rigidity asset of the lane is simultaneously available.
  sl3z-regular-microstates-are-congruence-correctable: that is the correctability hole at n = 3; the same hole instantiated here is the one place a cohomological attack (normalized-HS DGLT criterion over reduced (T_2) vanishing) has existing literature footing.
---

Let `Lambda = SL_5(Z)`, `Gamma = SL_5(Z[1/2])`,
`h = diag(2, 1, 1, 1, 1/2)`.  Claim `(RC5)`: in every tracial matrix
ultraproduct `M` and every trace-preserving regular-trace
representation `pi` of `Gamma`,

```text
pi(SL_5(Z))' cap M = pi(SL_5(Z[1/2]))' cap M.                   (RC5)
```

**The lane transports verbatim.**  Center of `Gamma` is trivial
(`zeta^5 = 1` in `Z[1/2]` forces `zeta = 1`), `Gamma` is ICC, the
pair is co-dense (CSP + superrigidity, identical citations to the
`n = 3` instance), commensurated with Schlichting completion
`PSL_5(Q_2)` (Howe--Moore, property (T)), and `Gamma = <Lambda, h>`
by expanding conjugation.  Consequently every established theorem of
the lane holds here with unchanged proofs:
`hecke-far-commutator-defect-formula` (any rank),
`hecke-averaging-realizes-commutant-expectation` and
`one-commutator-controls-distance-to-full-commutant` (`n >= 3`; the
coset count becomes `L = p . #{incident line-hyperplane pairs}` by
the same mod-`p^2` parahoric computation, the parabolic now of type
`(1, n-2, 1)`), `rcc-carrier-character-face-compression` and
`hnn-carrier-enemy-moment-splitting` (odd `n`, trivial center),
`projective-far-defect-formula`, and the sector closure
`odd-congruence-lambda-exact-sector-collapses` -- the diagonal of
`SL_5` has Weyl orbit of size twenty and in particular the same
three-term relations, so the corrector evaluation `W = 1` runs
verbatim.  By `hnn-route-is-relative-commutant-collapse` (general
pair form, established), `(RC5)` makes
`G_5 = < SL_5(Z[1/2]), t | [t, SL_5(Z)] = 1 >` a finitely presented
non-hyperlinear group.

## Attempts

- **Why add a third instance.**  Bader--Sauer (arXiv:2308.06517):
  `SL_N(Z)` has property `(T_(N-2))` -- reduced vanishing of unitary
  cohomology up to degree `N - 2` -- so degree-2 vanishing holds for
  `N >= 4` and fails to be provable at `N = 3` (sharp non-vanishing
  at degree `N - 1` for `N in {3, 4}`, arXiv:2410.22310).  The
  correctability hole and any DGLT-style normalized-HS criterion
  therefore have literature infrastructure exactly at `N >= 4`; among
  those, `N = 5` keeps the trivial-center/odd-`n` hypotheses of the
  established lane theorems, making it the canonical deep instance.
  (`N = 4` works too, at the cost of routing every statement through
  the finite center `{+-1}` via the chi-face machinery.)
- **All four last-missing holes instantiate.**  The single-average
  isometry, factorial carrier characters, projective transfer and
  congruence correctability each make sense verbatim at `n = 5`, and
  any ONE of them at ANY admissible `n` reaches the goal; the
  instances are independent chances, not duplicated work, because
  the cohomological assets differ with `n` while the Weyl mechanism
  does not.
- **Falsification honesty.**  Nothing here makes `(RC5)` easier to
  refute or prove per se; the instance exists so that degree-2
  cohomological technology, if and when it acquires a normalized-HS
  form, lands on a pair where the rest of the lane is already
  theorem.
