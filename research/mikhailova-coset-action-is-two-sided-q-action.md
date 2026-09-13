---
rg: 2
id: mikhailova-coset-action-is-two-sided-q-action
kind: claim
title: The Mikhailova coset action is the two-sided translation action of the base, sofic whenever the base is amenable
distinct_from:
  fiber-product-conjugation-action-lemma: that is the fiber product T x_Q T acting on the KERNEL N with diagonal stabilizer; this is the FULL product F x F acting on the COSETS of the fiber-product SUBGROUP M, whose coset space is Q with the two-sided translation action.
  compiler-rope-is-coset-wreath-of-an-a-t-menable-base: that reframes the positive branch as a coset wreath and records that no known nonsoficity mechanism applies; this computes the coset action explicitly and proves it is sofic for an amenable edge base.
  centralizing-hnn-is-residually-finite-iff-edge-is-separable: that decides residual finiteness of the centralizing HNN by separability of the edge; this concerns soficity of the coset action underneath it, which amenability of the base gives even though the edge is non-separable.
---

ESTABLISHED (unreviewed).  Let `Q = <X | R>` be finitely presented,
`F = F(X)`, `phi : F ->> Q`, and let

```text
M = M_Q = { (u,v) in F x F : u =_Q v } = (phi x phi)^(-1)(Delta Q)
```

be the Mikhailova subgroup.  Then the coset action of `F x F` on `(F x F)/M`
is, canonically,

```text
(F x F)/M  ~=  Q,     (a,b) M  <->  phi(a) phi(b)^(-1),
(g,h) . q  =  phi(g) * q * phi(h)^(-1),                               (TS)
```

i.e. the **two-sided translation action** of `Q x Q` on `Q = (Q x Q)/Delta Q`,
pulled back along `phi x phi`.  The point stabilizer of `1 in Q` is `M`.

**Consequence: an amenable base makes the coset action sofic.**  If `Q` is
amenable, the coset action `F x F curvearrowright (F x F)/M` is a sofic action
on a set — even though `M` is non-separable when `Q` has unsolvable word
problem.  Hence, via [[centralizer-hnn-is-free-generalized-wreath]], the
centralizing HNN base `< F x F, v | [v, M] = 1 > = Z wr^*_((F x F)/M) (F x F)`
is a free `Z`-lamp wreath over a sofic coset action.

DERIVATION [[mikhailova-coset-action-two-sided-proof]].

## Why this matters for the compiler

The positive branch of [[sofic-safe-finite-presentation-compiler]] needs the
inner rope `< K_e, v | [v, L_e] = 1 >` sofic, with `L_e` a Mikhailova-type
subgroup ([[compiler-rope-is-coset-wreath-of-an-a-t-menable-base]]).  By (TS)
the base of the rope is governed by the group `Q` whose word problem the edge
encodes.  There exist **finitely presented amenable** (indeed solvable) groups
`Q` with unsolvable word problem (Kharlampovich, *A finitely presented
solvable group with unsolvable word problem*, Izv. Akad. Nauk SSSR 45 (1981)),
and the Mikhailova construction is agnostic to the choice of `Q`.  Choosing
such an amenable `Q`:

- keeps `M_Q` finitely generated and non-separable (undecidable membership),
  so the edge is still non-separable and the quotient-model no-go
  ([[centralizing-hnn-sofic-via-regular-edge-centralizer]]) still holds;
- yet makes the coset action `(F x F) curvearrowright (F x F)/M_Q` sofic by the
  consequence above.

So the edge-base contribution to the positive-branch obstruction can be
**removed by design**.  What remains is exactly the free-`Z`-lamp step over an
already-sofic coset action — the perturbed-edge Britton lemma
[[centralizing-hnn-perturbed-edge-separation]], equivalently a free-wreath
analogue of the Gao--Kunnawalkam Elayavalli--Patchell direct-sum wreath
theorem.  Whether the compiler's INF/FIN switch and negative branch can be
carried with an amenable Mikhailova base is a separate check; (TS) and the
amenable-base soficity are unconditional.
