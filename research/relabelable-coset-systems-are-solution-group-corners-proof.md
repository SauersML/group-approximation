---
rg: 2
id: relabelable-coset-systems-are-solution-group-corners-proof
kind: route
title: Rename generators, Fourier-transform each abelian fibre, and read the coset relations as central phase relations
target: relabelable-coset-systems-are-solution-group-corners
requires: []
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-relabeling-collapse-2026-09-13.md
---

The complete proof is §2 of the artifact.

**1. Only the relation sets matter.**  `A(S)` is presented by projections
`p_q^s`, row sums one, and `p_q^s p_(q')^(s') = 0` for `(s,s') notin R_(qq')`.
Renaming `s |-> β_q(s)` gives the presentation of `A(S^β)`.

**2. Fourier transform.**  In `A(S^β)` put
`X_(q,χ) = sum_a χ(a) p_q^a` for `χ in Â_q`.
- These are unitaries representing `Â_q`.
- Take `(χ,χ') ⊥ D` and `c = c^β_(qq')`.  Products `p_q^a p_(q')^(a')`
  vanish off `cD`, the character `χ (x) χ'` equals the constant
  `(χ (x) χ')(c)` on `cD`, and all products sum to `1`.  So
  `X_(q,χ) X_(q',χ') = (χ (x) χ')(c)`.
- This gives `C^*(Γ)/<J-ω> -> A(S^β)`.

**3. Converse.**  Put `P_q^a = |A_q|^(-1) sum_χ conj(χ(a)) x_(q,χ)`; these
are PVMs.
- Averaging the cross relations over `ψ in D^⊥`, with
  `|D^⊥|^(-1) sum_ψ ψ(y) conj(ψ(c)) = 1_(cD)(y)`, gives
  `sum_(y notin cD) P_q^(y_1) P_(q')^(y_2) = 0`.
- Multiply on the left by `P_q^a` and on the right by `P_(q')^(a')`.  This
  isolates `[(a,a') notin cD] P_q^a P_(q')^(a') = 0`.
- The two maps are inverse on generators.
- `C^*(Γ)/<J-ω> = p_ω C^*(Γ)`, since `J` is central with `J^n = 1`.

**4. Nonhyperlinearity.**
- A tracial state gives a representation of `Γ` with `J = ω`.  So
  `J^j != e` for `0 < j < n`, and `τ_reg(p_ω) = 1/n`.
- If `Γ` were hyperlinear, `p_ω L(Γ) p_ω` would embed in a corner of `R^U`
  of trace `1/n`, which is isomorphic to `R^U`.
- Then `A(S) ≅ p_ω C^*(Γ) -> p_ω L(Γ) p_ω` would be an `R^U` model.

**5. Single relations.**  Take a Goursat coset over `(K_1 ⊇ N, K'_1 ⊇ N')`
with matched cells.
- Label `K_q` by a cyclic group of order `|K_q|`.  Send `c_1 K_1` to a coset
  of its subgroup of order `|K_1|`, and the `N`-cells to cosets of its
  subgroup of order `|N|`.
- Do the same on the other side.
- Relabel cells so that the cell matching is the identity of the cyclic
  quotient.
- The relation is then the graph of a quotient isomorphism, which is a coset.
