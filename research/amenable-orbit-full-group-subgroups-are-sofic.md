---
rg: 2
id: amenable-orbit-full-group-subgroups-are-sofic
kind: claim
title: Groups of bounded piecewise translations of an essentially free measure-preserving amenable action are sofic
distinct_from:
  cuntz-groupoid-admits-no-folner-sequence: That shows Ma's topological Folner theorem cannot reach V, because the Cuntz groupoid has no Folner sequence; this is the measure-theoretic certificate, which needs an invariant probability measure instead of topological Folner sets and certifies every subgroup of the full group at once.
  labbe-shift-derived-full-group-escapes-known-obstructions: That checks which obstructions fail for one Z^2 shift; this proves the positive property, soficity, for every group acting by bounded piecewise translations of any essentially free measure-preserving action of any amenable group.
---

**ESTABLISHED.**

**Setting.**
- `Lambda` is a countable amenable group acting on a standard probability space
  `(X, mu)` by measure-preserving Borel automorphisms, essentially freely: the
  set `X_free` of points with trivial stabilizer has measure one.
- `W(Lambda ~ X)` is the group of Borel bijections `g` of `X` for which there is
  a Borel map `c_g : X -> Lambda` with **finite range** and `g(x) = c_g(x) x`
  for every `x`. Such a `g` preserves `mu`, since it translates each piece
  `{c_g = lambda}` by an element of `Lambda`.

**Theorem.** Let `Gamma` be a countable group and `rho : Gamma -> W(Lambda ~ X)`
a homomorphism with `mu(Fix rho(g)) < 1` for every `g != 1`. Then `Gamma` is
sofic. More precisely, `Gamma` has almost-actions on finite sets whose
fixed-point proportions converge to `mu(Fix rho(g))` for every `g`.

**Corollary (topological full groups).** Let `Lambda` be amenable and act on a
compact metrizable space `X` by homeomorphisms, with an invariant Borel
probability measure `mu` of full support for which the action is essentially
free. Then every subgroup of `[[Lambda ~ X]]` is sofic. Indeed a nontrivial
element moves a nonempty open set, which has positive measure, and a
continuous cocycle on a compact space has finite range.

**Instances.**
- Every subgroup of `[[Z^d ~ X]]` for a free minimal `Z^d`-subshift `X`: an
  invariant measure exists because `Z^d` is amenable, and it has full support
  by minimality. This includes `D([[Z^2 ~ Omega_U]])` for Labbé's shift, whose
  soficity is already noted in `labbe-shift-derived-full-group-is-finitely-presented`
  through an Elek--Szabó remark in Elek--Monod.
- Every countable group of interval exchanges or polygon exchanges translating
  by elements of a countable abelian group that acts essentially freely.

**What is new here.** Nothing about the statement: soficity of full groups of
amenable orbit relations is folklore (Elek--Szabó; Elek, arXiv:1211.0621, for
sofic relations). The proof in the route is self-contained. It uses only Følner
sets of `Lambda`, a law of large numbers, and tensor amplification; it avoids
Ornstein--Weiss hyperfiniteness. The node exists so that the finitely presented
simple question can consume it: see `fp-simple-group-in-amenable-orbit-full-group`.

Proof: `amenable-orbit-full-group-subgroups-sofic-proof`.
