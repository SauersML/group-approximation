---
rg: 2
id: sp4-metaplectic-class-pointwise-coboundary-limit
kind: claim
title: The metaplectic scalar class of the symplectic lattice is a pointwise limit of coboundaries
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is the lifting-property hole; this is the single cocycle question its Ioana--Spaas--Wiersma attack reduces to at the base case, and a positive answer REFUTES that hole.
  deligne-central-mark-hs-collapse: that asks whether vanishing normalized-HS presentation defect forces the Deligne central mark to collapse in almost-representations; this is the exact-cocycle analogue — whether the class itself can be approximated by coboundaries pointwise on the group — with no representation or defect present.
  bcs-projective-kernel-phase-compilation: that compiles a projective-kernel phase into a BCS predicate for compiler purposes; this is an arithmetic cocycle-rigidity question about one classical class of Sp_4(Z).
---

OPEN CLAIM (either answer is a theorem someone wants).  Let
`Gamma = Sp_4(Z)` and let `c_pi in Z^2(Gamma, T)` be a cocycle
representing the metaplectic class: the image of Deligne's integral class
under `H^2(Gamma, Z) -> H^2(Gamma, T)` composed with `n -> e^(i pi n)`
(the class of the double cover of `Gamma` inside `Mp_4(R)`).  Question:
is there a sequence of maps `b_n : Gamma -> T` with

```text
b_n(g) c_pi(g,h) b_n(h) b_n(gh)^(-1) --> 1  pointwise on Gamma x Gamma?  (MC1)
```

Equivalently: does the fixed class `[c_pi]` lie in the pointwise closure
of the coboundaries `B^2(Gamma, T)` inside `Z^2(Gamma, T)`?

**YES refutes the Sp_4 LLP hole.**  Ioana--Spaas--Wiersma Theorem A
(arXiv:2006.01874, read at source 2026-08-21) refutes LLP of `C^*(Gamma)`
from: a relative-(T) pair (take `Lambda = Gamma`, property (T)); cocycles
`c_n -> 1` pointwise, each with `c_n|_Lambda` not a coboundary (take the
`(MC1)` representatives, all in the fixed nontrivial class); and — the
load-bearing condition — a finite-dimensional projective representation
with cocycle exactly `c_n` for each `n`.  The finite Weil representations
of `Sp_4(Z/2^k)` supply finite-dimensional projective representations of
`Gamma` in the metaplectic class (the double cover of `Gamma` is its
residually-finite central quotient), and twisting by the maps `b_n`
realizes each `(MC1)` representative exactly.  So YES would prove
`C^*(Sp_4(Z))` fails LLP, closing Fournier-Facio--Willett's higher-rank
(L)LP question negatively at its base case
(`sp2g-z-full-c-star-algebra-has-llp` records why `g = 2` is the base).

**Why Theorem A cannot run without this claim.**  On the circle of scalar
classes `chi_theta` (fix an integer-valued representative `c_Z` of the
Deligne class; `c_theta = e^(i theta c_Z)`), conditions (1)-(2) of
Theorem A are automatic: `c_theta -> 1` pointwise as `theta -> 0` and the
classes are nontrivial for generic `theta`.  What fails is
finite-dimensional realizability: by Deligne's congruence-closure theorem
(the in-repo order-three case is
`deligne-triple-cover-fd-central-invisibility`: every finite-dimensional
unitary representation of the cover kills the central mark), every
finite-dimensional projective representation of `Gamma` over the Deligne
circle has cocycle class `theta in {0, pi}`.  So the only way to feed
Theorem A is the CONSTANT class `theta = pi` with pointwise-vanishing
representatives — exactly `(MC1)`.  This is the precise reason the
higher-rank LLP question is open at `Sp_4(Z)` while `Z^2 rtimes SL_2(Z)`
fell: there the finite Weil classes accumulate at the trivial class
through infinitely many distinct finite-dimensionally realized levels,
here Deligne invisibility pins all realizable classes to two points.

**NO is a new rigidity theorem.**  A negative answer says the metaplectic
class is uniformly separated from coboundaries in the pointwise topology
— a cocycle-rigidity statement for `Sp_4(Z)` that would be a necessary
step toward LLP of `C^*(Sp_4(Z))` (`non-hyperlinear-from-sp2g-llp`) and
is of independent interest as an exact-cocycle strengthening of the
Deligne lane's `deligne-central-mark-hs-collapse`.

## Attempts

- **Relation to Dogon's Theorem 3.1** (arXiv:2211.10492): a sequence of
  nontrivial scalar cocycles converging pointwise to `1` whose twisted
  group von Neumann algebras are all Connes embeddable refutes weak
  ucp-stability of a (T) group.  With `(MC1)`, all `c_n` lie in the
  metaplectic class, whose twisted algebra `L_(c_pi)(Gamma)` is a corner
  of `L(Gamma~/2Z)` with `Gamma~/2Z` residually finite, hence Connes
  embeddable.  So YES also refutes weak ucp-stability of `Sp_4(Z)` — the
  hypothesis of `dogon-sp2g-weak-ucp-nonhyperlinear` at `g = 2` — making
  the two conditional `g = 2` routes stand or fall together with this
  single cocycle question.  (For `g >= 3` both are already dead or fenced:
  LLP by the `SL_g(Z)` subgroup; flexible stability remains the open
  `Sp_2g` case of Dogon's abstract.)
- **What is actually known about `B^2(Gamma, T)`'s closure.**
  Ioana--Spaas--Wiersma Corollary E gives LP failure from
  `H^2(Gamma, R) != 0` (their Example 1.3(i) states it verbatim for
  `Sp_2n(Z)`, `n >= 2`), and their Remark 1.1 shows LP would force
  coboundaries to be OPEN in `Z^2` with `L^0` coefficients; neither
  decides the pointwise closure question for the fixed scalar class.  No
  computation is recorded in either direction; the natural first probe is
  quantitative: over the congruence quotient `Sp_4(Z/2^k)`, minimize
  `max_(g,h in F) |b(g) c_pi(g,h) b(h) b(gh)^(-1) - 1|` over `b` for a
  small window `F` and growing `k`, watching whether the optimum decays
  or stabilizes — a finite, well-posed optimization on each level.
