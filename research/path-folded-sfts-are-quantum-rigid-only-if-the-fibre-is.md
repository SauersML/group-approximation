---
rg: 2
id: path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is
kind: claim
title: An SFT that contains every fold of a fibre SFT along one skeleton configuration by a 1-Lipschitz surjection is quantum rigid only if the fibre is; so the Aubrun–Bitar–Huriot-Tattegrain minimal free SFT on F_n x Z is rigid only if its Z^2 fibre is
requires:
  - free-times-z-carries-a-minimal-free-sft
  - free-group-boundary-shifts-are-quantum-rigid
distinct_from:
  free-times-z-carries-a-minimal-free-sft: that imports existence of a minimal free SFT on F_n x Z from ABHT's path-folding construction; this tests that construction for quantum rigidity and pins its rigidity to the rigidity of the folded Z^2 shift.
  quantum-rigidity-passes-to-sub-sfts: that passes rigidity from an SFT to its sub-SFTs over the same group; this passes rigidity from a total shift over one group to a fibre shift over another group, along a Lipschitz fold.
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that asks whether rigidity passes UP from a Z^r fibre to its Busemann transplant over a building lattice; this proves the DOWN direction for every fold, including Busemann transplants, so rigidity of the fibre is necessary there too.
  quantum-rigidity-is-product-stable: that is the special case where the fold is a coordinate projection of a product group and the skeleton is trivial.
---

**ESTABLISHED** through `path-folded-sft-rigidity-pullback-proof` (lane bh-g2-fixedpoint-b,
2026-09-18; elementary lane proof, not reviewed; no priority claimed). Quantum families (Q1–Q3)
and `D`-quantum rigidity are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`.

## Fold lemma

**Setting.**
- `Λ`, `Λ'` are finitely generated groups with word metrics.
- `X ⊆ A^(Λ')` is an SFT (the *fibre*), and `Z ⊆ (A × B)^Λ` is an SFT (the *total shift*).
- There are a *skeleton* `y ∈ B^Λ` and a surjection `β: Λ → Λ'` that is 1-Lipschitz, i.e.
  `d(β(g), β(g')) <= d(g, g')`, such that the fold `x∘β ⊗ y`, defined by
  `g ↦ (x(β(g)), y(g))`, lies in `Z` for every `x ∈ X`.

`β` need not be a homomorphism or equivariant.

**Statement.** If `Z` is `D`-quantum rigid over a field `k`, so is `X`, with the same `D` and `k`.

**Mechanism.** Pull a `D`-family `F_a(z)` of `X` back to `E_(a,b)(g) = [b = y(g)] · F_a(β(g))`.
- The skeleton idempotents are scalars, so they are automatically classical.
- 1-Lipschitz carries (Q2) over.
- Every fold lies in `Z`, which carries (Q3) over.
- `β` is surjective, so any noncommuting pair of `F` reappears in `E`.

## Application: the ABHT path-folding shift on `F_n × Z`

This is the construction of arXiv:2204.11492v3, §5, TeX l.559–785, read at source; lane copy
md5 `5e2f7f7e…`.
- **The flow layer.** `Y_f` is the end shift of `F_n` made constant along `Z`. As an SFT it is
  `X_∂(F_n) ⊠ pt`, so it is quantum rigid by `free-group-boundary-shifts-are-quantum-rigid` and
  `quantum-rigidity-is-product-stable`.
- **The fibre.** `X` is a minimal, strongly aperiodic, horizontally expansive (thickening 0) Wang
  SFT on `Z^2`. ABHT obtain it from the minimal aperiodic SFT `X_0` of Labbé–Mann–McLoud-Mann
  (their Theorem `theorem:SFT_Labbe`) by a higher-block recoding and a rotation by `π/2`. Whether
  `X_0` is main's `Ω_U` was not checked.
- **The fold.** Let `W` be the word of `y ∈ Y_f`. For `g = w t^i`, put `β(g) = (i, j(w))` with
  `j(w) = 2 max{|u| : u a common prefix of w and W} − |w|`. This is a Busemann function of the
  end `W`, plus the `Z`-coordinate. Their Proposition `configsJuntas` says exactly that
  `x∘β ⊗ y ∈ Z` for every `x ∈ X`.
- **Hypotheses of the lemma.** `β` is 1-Lipschitz, since `t` moves `i` by 1 and each tree
  generator moves `j` by `±1`. It is onto `Z^2`, since `j` takes every value along the line
  `ρ_W`.

**Corollary.** If the ABHT shift `Z` is `D`-quantum rigid over `k`, then `X` is `D`-quantum rigid
over `k`. Then:
- `X_0` is rigid at large scale, since rigidity at large scale is a conjugacy invariant for
  `Z^2`-SFTs (`sft-crossed-product-fp-iff-quantum-rigid`);
- `LC(X_0, k) ⋊ Z^2` is finitely presented;
- `X_0` is an instance of `free-minimal-z2-sft-is-quantum-rigid`.

So over `F_n × Z` this construction answers gate G2 only if the amenable `Z^2` gate G2(a) is
answered for one horizontally expansive minimal free `Z^2`-SFT.

**The same holds for** the finite-index lifts of their Proposition `prop:normal_finite_index_lift`
(unimodular GBS groups, torus knot groups, `BS(n,n)`), and for their `BS(2,3)` fold of a
hyperbolic-plane tiling, whose fibre is the plane tiling. It also holds for any Busemann transplant
`y∘M^(-1)∘b_c` whose transplant map is 1-Lipschitz and onto (the setting of
`busemann-transplants-give-free-sfts-on-building-lattices`). There the fibre's rigidity is
**necessary**, not only assumed.

## What is not proved: the converse

The converse, "`X` rigid implies `Z` rigid", is the open claim
`path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid`. Two first steps are proved in its
Attempts section:
- the flow marginals of every quantum family on `Z` commute;
- horizontal expansivity gives operator-level row determinism, so on every classical flow sibling
  past branches carry equal letter operators.

What remains is the centrality of the flow marginals, the same step (C) that
`busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid` leaves open.

## Lesson for general BH

**Folds import the fibre's rigidity problem unchanged.** Path-folding and Busemann transplants
realise every fibre configuration along a 1-Lipschitz map. So a noncommuting family of the fibre
over the amenable factor is a noncommuting family of the total shift at the same scale.

**Non-amenable tree directions give rigidity only along themselves.** They supply compression
rigidity of the skeleton for free (`free-group-boundary-shifts-are-quantum-rigid`), and they give
freeness through the skeleton's aperiodic fibre. They cannot certify the fibre: the metric along
the `Z` factor of `F_n × Z` is untouched by the tree.

**What this means for G2 over one-ended non-amenable envelopes.** Existence (ABHT) and skeleton
rigidity are supplied. What is missing is exactly the `Z^2` (or `Λ_0`) fibre gate, plus the
transfer (C). A design that wants non-amenability to do the rigidity work must entangle the
fibre's letters with the tree directions themselves, not carry them along a flow.

DERIVATION
path-folded-sft-rigidity-pullback-proof
