---
rg: 2
id: cantor-diagonal-two-generation-proof
kind: route
title: Disjointify the ample groupoid and cut corners with spectral projections
target: cantor-diagonal-algebras-are-two-generated
requires: []
---

The Weyl groupoid `G` of a C\*-diagonal is principal, étale,
Hausdorff, with unit space the Cantor set, hence AMPLE: compact open
bisections form a basis.  `G ∖ X` is σ-compact, so it is covered by
countably many compact open bisections, and successive differences
(compact opens are closed under difference here) give a PARTITION
`G ∖ X = ⨆_n B_n` into compact open bisections.  Choose normalizers
`v_n ∈ A` implementing `B_n` (sections of the twist over `B_n`); then
`A = C*(D ∪ {v_n})` since the `B_n` cover all arrows.  Fix summable
weights `c_n > 0` and set `b := Σ c_n v_n`.

**Recovery of each `v_n` from `(d_0, b)`.**  Fix `N` and `ε`, and
work with `B_1, …, B_M` where `Σ_{m>M} c_m < ε`.  Principality gives:
between any two unit-space points there is AT MOST ONE arrow.  Each
`B_m` is compact with `r(γ) ≠ s(γ)` pointwise (no isotropy off the
units), so `r` and `s` are uniformly separated on `B_m`; a fine
clopen partition `{X_j}` of `X` therefore splits each `B_m` (`m ≤ M`)
into finitely many pieces whose source atom differs from their range
atom, and — again by principality plus compactness, refining once
more — so that any ordered atom pair `(X_i, X_j)` carries a piece of
AT MOST ONE of `B_1, …, B_M`.  The atoms are clopen, so their
indicators are continuous functions of `d_0`:
`χ_j = 1_{X_j}(d_0) ∈ C*(d_0)`.  Then for an atom pair `(i, j)`
carrying the piece `P ⊆ B_m`,

```text
χ_i b χ_j = c_m · (χ_i v_m χ_j)  +  (tail of norm < ε),
```

because every other `B_l` (`l ≤ M`) contributes zero to this corner
and the `l > M` terms total less than `ε`.  So each piece
`χ_i v_m χ_j` lies within `ε/c_m` of `C*(d_0, b)`; summing the
finitely many pieces of `B_m` and letting `ε → 0` (with refinements
per stage) yields `v_m ∈ C*(d_0, b)` exactly.  Hence
`C*(d_0, b) ⊇ D ∪ {v_n} ` and equals `A`.

**Model checks.**  `M_2` with its diagonal: one arrow-pair, `b = ce_{12}`,
`C*(diag(1,2), e_{12}) = M_2`.  A minimal free Cantor system
`C(X) ⋊ Z`: the pieces of the canonical unitary are recovered from
one weighted sum of its clopen cutdowns, as expected.

**Residue.**  From three self-adjoints (`d_0, Re b, Im b`) to a
single generator is the classical 2-to-1 step `a + ib` once the pair
`(d_0, b)` is replaced by two self-adjoints generating the same
algebra; whether `d_0` can always be absorbed into one of them (e.g.
`C*(d_0 + iλ·Re b, Im b)` for generic `λ`) is left open here — the
theorem as stated gives 2-generation, already strictly stronger than
anything recorded on the Cartan question.  Non-principal Cartans are
genuinely outside the method: isotropy arrows are invisible to
diagonal corner-cutting.
