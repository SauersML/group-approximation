---
rg: 2
id: square-module-elementary-centre-is-central-units
kind: claim
title: Over a ring isomorphic to its square the centre of every elementary group is the group of central units, so finitely presented simple projective hosts of that kind have finite centre
distinct_from:
  projective-elementary-fp-kernel-criterion: that splits finite presentation of PE_n(R) into finite normal generation of the Steinberg kernel and finite generation of Z(E_n(R)); this computes the second group for square-module rings as Z(R)^x, so that clause becomes a property of the commutative ring Z(R).
  rank-four-elementary-center-obstructs-simplicity: that exhibits the single involution -I_4 in E_4(L) when 2 != 0; this shows that over R = R^2 every central unit is an elementary scalar, and uses finite generation rather than simplicity to force a finite centre.
  square-module-ring-hosts-are-sandwich-ring-quotients: that turns a square-module ring host into a sandwich-ring witness; this is a necessary condition on such hosts, namely a finite centre when the ring is simple.
  leavitt-tensor-steinberg-kernel-is-stable-k2: that treats the kernel half of the Leavitt tensor criterion; this is the centre half, and explains why the base field there must be finite (and is F_2 when E_n itself is to be simple).
  f2-steinberg-elementary-groups-have-no-middle-mf-regime: that uses a trivial scalar centre over F_2 as an input; this computes the scalar centre for every square-module ring.
---

**ESTABLISHED.** Let `R` be a unital associative ring with `R_R ≅ R_R^d` as
right modules for some `d >= 2`, and let `n >= 2`.

1. **Scalars are elementary.** For every central unit `c in Z(R)^x`,
   `c^(d-1) I_n in E_n(R)`.
2. **Centre.** `Z(E_n(R)) = { c I_n : c in Z(R)^x, c I_n in E_n(R) }`, and it
   contains `(Z(R)^x)^(d-1) I_n`. If `d = 2` then `Z(E_n(R)) = Z(R)^x I_n ≅ Z(R)^x`.
3. **Finite centre.** Suppose moreover that `R` is finitely presented and simple,
   `n >= 4`, and `PE_n(R) = E_n(R)/Z(E_n(R))` is finitely presented. Then `Z(R)` is
   a finite field `F_q`.
4. **Simplicity of E_n itself.** If `E_n(R)` is simple, then every central unit
   satisfies `c^(d-1) = 1`. For `d = 2` this means `Z(R)^x = 1`. For a simple
   `R` it means `Z(R) = F_q` with `q - 1 | d - 1`, so `Z(R) = F_2` when `d = 2`.

## What it kills

**Invariant:** the scalar subgroup `(Z(R)^x)^(d-1) I_n`. It is central in
`E_n(R)`, and it is elementary because `K_1` cannot see scalars on a square
module (`[c] = d[c]` in `K_1(R)`).

**Where it dies:** clause (c), "`Z(E_4)` finitely generated", of
[[ck-sandwich-ring-has-fp-projective-simple-quotient]]. Equivalently, it dies at
clause 2 of [[projective-elementary-fp-kernel-criterion]].

- **Infinite centre.** Every simple, finitely presented, square-module
  candidate host whose centre is an infinite field fails finite presentation
  of `PE_n`. This includes every such ring of characteristic `0`: a simple ring
  containing `Z` has a centre containing `Q`. It also includes `B ⊗ L_K(1,d)`
  with `B` central simple over an infinite field `K`. In particular a simple
  square-module ring host of an integral group ring `Z[H]`, as sought in
  [[decidable-group-ring-has-fp-projective-simple-host]], cannot exist.
- **Base field of the Leavitt tensor lane.** The base field there must be
  finite. When `E_n` itself (not `PE_n`) is required to be simple, it must be
  `F_2`. So the choice of `F_2` is forced, not merely convenient.
- **Sufficient branch.** For `d = 2` the sufficient branch of the hole becomes
  a sharper decomposition, because clause (c) is now a statement about
  `Z(R)^x` alone. A finitely presented `R ≅ R^2` has `PE_4(R)` finitely
  presented iff `ker(St_4(R) -> E_4(R))` is finitely normally generated and
  `Z(R)^x` is finitely generated.

## What it does not cover

- **Rings that are not square-module.** It says nothing about properly
  infinite rings with `R_R ≇ R_R^d`. Examples are Leavitt path algebras whose
  `K_1` detects scalars, and the Dedekind-defect witnesses of the R4 regime
  in [[ck-maximal-kernel-four-regimes]].
- **A possible extension.** For purely infinite simple `R` with `[1]` torsion
  in `K_0`, Ara--Goodearl--Pardo give `R ≅ R^(m+1)`, so this claim would apply.
  That result has not been imported into the graph.
- **Not simplicity itself.** Item 3 is a necessary condition only. A finite
  centre does not give simplicity or finite presentation.

DERIVATION
[[square-module-elementary-centre-is-central-units-proof]]
