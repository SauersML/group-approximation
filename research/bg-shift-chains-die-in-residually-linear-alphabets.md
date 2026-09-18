---
rg: 2
id: bg-shift-chains-die-in-residually-linear-alphabets
kind: claim
title: A forward Baumslag--Gersten chain is trivial in every residually periodic, residually linear, residually solvable or compact group, so the Magnus shift dictionary for BG needs an exotic amenable alphabet
distinct_from:
  bg-cycle-triviality-is-closed-under-the-pbh-calculus: that treats finite BG cycles, which live in a finitely generated subgroup, so residual finiteness of finitely generated linear groups applies; this treats infinite forward chains, which need not lie in any finitely generated subgroup, and proves triviality in linear groups by a Jordan-decomposition argument, and in residually solvable groups by perfectness.
  nonsingular-magnus-extremes-separable-piece-sofic: its section 9 kills periodic alphabets and suggests U(m) alphabets as the way out; this kills U(m), every compact group, every linear group over any field, and every residually solvable group.
  baumslag-gersten-group-is-neither-linear-nor-self-similar: that says every finite image of BG kills a; this is about homomorphisms of the Magnus kernel of BG, which do not extend to BG and are what the shift dictionary uses.
artifacts:
  - research/bg-shift-chains-die-in-residually-linear-alphabets-proof.md
---

ESTABLISHED (written proof, unreviewed). Proof:
[[bg-shift-chains-die-in-residually-linear-alphabets-proof]].

**Definition.** A *forward BG chain* in a group `Q` is a sequence
`(x_j)_(j >= 0)` with

    x_(j+1)^(-1) x_j x_(j+1) = x_j^2     for all j >= 0.

**Theorem.** Let `R` be the class of groups that are residually (periodic, or
linear over some field, or solvable), with the factor type allowed to vary.
If `Q` is in `R`, then every forward BG chain in `Q` is trivial.

In particular this holds for every residually finite group, every linear
group over any field, every compact group (Peter--Weyl), and every residually
solvable group.

**Corollary (shift dictionary for BG).** Let `BG = <a,t | a^(a^t) = a^2>`, with
Magnus rewriting `W_0 = a_1^(-1) a_0 a_1 a_0^(-2)`. A shift representation
`rho : BG -> Q^Z rtimes Z`, `a -> x`, over an alphabet `Q` in `R` has
`rho(a) = 1`. So hypothesis (AA) of
[[amenable-alphabet-magnus-shift-dictionary-sofic]] can hold for BG only with
an amenable `Q` outside `R`. Examples of groups outside `R` are locally
solvable groups of unbounded derived length and infinite simple groups that are
not linear.

## Proof in outline

* **Quotients.** The image of a chain under a homomorphism is a chain, so it is
  enough to treat the three factor types.
* **Periodic.** This is the descending-prime argument of section 9 of
  [[nonsingular-magnus-extremes-separable-piece-sofic-proof]].
* **Solvable.** The chain relation says `x_j = [x_j, x_(j+1)]`, with
  `[g,h] = g^(-1) h^(-1) g h`. So every `x_j` lies in the derived subgroup of
  `M = <x_j : j >= 0>`, and `M` is perfect.
  A perfect solvable group is trivial.
* **Linear.** `x_j ~ x_j^2` forces all eigenvalues to be roots of unity. In
  characteristic `p` this makes `x_j` of finite order. In characteristic `0`
  the unipotent part `u_j` satisfies `x_(j+1)^(-1) log(u_j) x_(j+1) = 2 log(u_j)`,
  so conjugation by `x_(j+1)` has eigenvalue `2`. That is impossible, because
  its eigenvalues are ratios of roots of unity. So `u_j = 1`, and the periodic
  case finishes.

## Why it matters

The shift dictionary was blocked at singular extremes by periodic alphabets,
and the recorded way out was infinite-order letters in `U(m)`. That way out is
closed: compactness, linearity and residual solvability each force the chain to
die. So the next test is a question about amenable groups that are neither
residually linear nor residually solvable:
[[bs12-extends-to-amenable-square-conjugation-chain]].
