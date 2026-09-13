---
rg: 2
id: kazhdan-group-algebra-tate-diagonal-is-kkg-equivalence
kind: claim
title: For torsion-free Kazhdan hyperbolic Γ, the Tate diagonal 1_T ⊗ C*_r(Γ) → 1_T ⊗ C*_r(Γ^p) is a KK^(Z/p)-equivalence
distinct_from:
  tate-norm-shift-is-kkg-trivial: that asks for triviality of the shift on the Tate part of every norm; this asks for the stronger statement that, for Kazhdan group algebras, the Tate part is exactly the diagonal image.
---

**OPEN.**  Let `p` be prime, `G = Z/p = <σ>`, `Γ` a torsion-free infinite
hyperbolic group with property (T), and `1_T` the Tate object.  The subgroup
inclusion `ΔΓ ≤ Γ^p` gives a `G`-equivariant \*-homomorphism
`Δ : τ(C*_r Γ) → C*_r(Γ^p)` (permutation action), `λ_γ ↦ λ_(γ, …, γ)`.  Is
`1_T ⊗ Δ` a `KK^G`-equivalence?

**What is proved about it (unreviewed;
`research/artifacts/uct-kk-norm-functor-2026-09-13-part3.md`).**
- Its cone `Z_Γ` has contractible restriction.  The phantom part of `Z_Γ` is
  the phantom part of `1_T ⊗ N(C*_r Γ)`.
- `Z_Γ ⋊ G` is the cone of the reduced crossed product map
  `1_T ⋊_r (ΔΓ × G) → 1_T ⋊_r (Γ ≀ G)`.
- The `σ`-fixed cosets of `ΔΓ` in `Γ^p` correspond to elements of order
  dividing `p`, so for torsion-free `Γ` only the trivial coset is fixed.
- By `hyperbolic-bcc-finite-wreath-products`, `Z_Γ ⋊ G` induces zero on
  `K_*(− ⊗ B)` for every separable `B`.  This is a sketch; the cellular
  localization step is not fully checked.
- For torsion-free a-T-menable `Γ` the analogue holds: everything lies in
  `B^G`, and the cone is contractible.

**Exact reformulation (lane ex3-uct-tate-diagonal, unreviewed;
`tate-diagonal-cone-is-weakly-contractible-wreath-object`).**
- **Setup.** Put `W = Γ ≀ G`, `H = ΔΓ × <σ>`, `ε = [ℓ²(W/H)] ∈ KK^W(C_0(W/H), C)`
  and `Y = cone(ε) ⊗ q^*1_T`.
- **Where `Y` vanishes.** `Y` is weakly contractible, and even contractible on `Γ^p`.
- **The crossed product.** `W ⋉_r Y ≅ Z_Γ ⋊ G`, with the dual `Ĝ`-actions.
- **The equivalence.** This claim holds iff `W ⋉_r Y ≃ 0` in `KK^Ĝ`.
- **K-invisibility.** It now follows rigorously from the Meyer–Nest obstruction functor, with no
  cellular localization, and it covers every coefficient algebra `B`. This supersedes the sketch
  bullet above.

**Why it matters.**
- **Positive answer.** The permutation actions on `C*_r(Γ^p)` give no
  separable counterexample to the Meyer–Nadareishvili converse at `Z/p`.
- **Negative answer.** Suppose the cone `Z_Γ` is not contractible. Either its
  crossed product is KK-nonzero but K-invisible, a new non-equivariant
  phenomenon on the `(1 − γ)`-parts, or it has a nonzero phantom part. The
  second case refutes `MN(all separable)` at `Z/p`.

## Attempts

* **K-theory with coefficients (passes, dies as a proof).**  Baum--Connes with
  coefficients for `Γ ≀ G` makes the diagonal a K-isomorphism with every
  trivial-action coefficient.  Promoting that to a KK-equivalence needs
  bootstrap-type objects.  It works on the `γ`-parts, which are cellular, and
  fails on the `(1 − γ)`-parts.  Those are nonzero for Kazhdan `Γ`, by
  Skandalis's non-K-nuclearity.
* **Induction–restriction of Hilbert modules (dies).**  Completing
  `C*_r(Γ^p)` over the conditional expectation onto `C*_r(ΔΓ)` gives a module
  `ℓ^2(Γ^p/ΔΓ) ⊗ C*_r Γ`.  Its fixed coset is the diagonal and all other orbits
  are free, which is the isotropy picture one wants.  But the index is
  infinite, so the left action is not by compacts, and no transfer class in
  `KK^G` results.
* **Descended γ-elements (reduction only).**  With the Kasparov--Skandalis
  `γ` for `ΔΓ × G` and `Γ ≀ G`, the question splits into the `γ`-parts, where
  the diagonal is an equivalence, and a map between the `(1 − γ)`-parts.  No
  invariant is known that sees KK-morphisms between these K-invisible parts.
  - **Update (ex3-uct-tate-diagonal).** The `(1 − γ)`-map is the crossed
    product of the single weakly contractible `W`-object `Y` above.
  - The `γ`-parts need no γ-element at all: `γ_W · Y = 0` already follows from
    weak contractibility (Meyer–Nest Thm. 8.3).
* **Split (ex3-uct-tate-diagonal, proved, unreviewed).**  This claim is
  equivalent to the conjunction of two open claims:
  - `kazhdan-tate-crossed-product-inclusion-is-kk-equivalence`, a
    non-equivariant KK statement;
  - `kazhdan-group-algebra-tate-part-has-no-phantom`.

  The route is `kazhdan-tate-diagonal-from-crossed-product-and-no-phantom`.
  `Y` vanishes on every visible subgroup
  (`wreath-tate-cone-vanishes-on-centralizer-and-amenables`), so an
  obstruction must live on non-induced Kazhdan objects.
