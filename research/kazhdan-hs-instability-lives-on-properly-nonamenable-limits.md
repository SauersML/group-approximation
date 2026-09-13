---
rg: 2
id: kazhdan-hs-instability-lives-on-properly-nonamenable-limits
kind: claim
title: HS-stability of a Kazhdan group reduces to asymptotic representations whose limit algebra has no amenable summand
distinct_from:
  character-rigidity-equals-hyperfinite-hs-stability: that is the Dogon--Vigdorovich equivalence for higher-rank lattices with (T;FD), proved through charmenability; this holds for every finitely generated Kazhdan group with no lattice input, and adds the reduction for limit algebras that are only partly amenable.
  steinberg-hyperfinite-hs-stable: that is hyperfinite HS-stability of one Leavitt Steinberg cover; this is the general Kazhdan statement together with the mixed-limit reduction.
  sl3-half-is-hyperfinite-hs-stable: that uses Peterson--Thom character rigidity for SL_3(Z[1/2]), which lacks (T); this uses property (T) and no character classification.
  kazhdan-weak-ucp-stability-is-flexible-stability: that removes the separating-input quantifier for hyperlinear Kazhdan groups; this removes every asymptotic representation whose limit algebra has an injective direct summand, and needs no hyperlinearity.
artifacts:
  - research/artifacts/solve-nh-word-stability-2026-09-13.md
---

**ESTABLISHED.** Let `Γ` be a finitely generated group with property (T).

**(A1) Amenable traces are atomic.** Let `φ` be a normalized trace on `Γ` whose GNS
von Neumann algebra `M_φ = π_φ(Γ)''` is injective (equivalently amenable). Then
`M_φ = ⊕_{i∈I} M_{k_i}(C)` with `I` countable, and `φ = Σ_i t_i · tr_{k_i} ∘ ρ_i`, where
the `ρ_i` are irreducible finite-dimensional representations, `t_i > 0` and `Σ t_i = 1`.
In particular `φ` is a pointwise limit of normalized traces of finite-dimensional
representations.

**(A2) Hyperfinite stability is automatic.** `Γ` is hyperfinitely Hilbert--Schmidt
stable in the sense of Dogon--Vigdorovich (arXiv:2506.20843v2, Definition
`def:hyp_HS_stab`).

**(A3) Reduction.** Let `ω` be a free ultrafilter on `N`. Call maps
`σ_n : Γ → U(d_n)` an *asymptotic representation along `ω`* if
`lim_ω ||σ_n(gh) − σ_n(g)σ_n(h)||_2 = 0` for all `g, h`. Call it *properly non-amenable*
if its limit algebra `N_ω = σ^ω(Γ)''` in the tracial ultraproduct `∏^ω (M_{d_n}, tr)` has
no nonzero injective direct summand. Then `Γ` is flexibly (resp. strictly) HS-stable
if and only if, for every `ω`, every properly non-amenable asymptotic representation
along `ω` admits genuine representations `ρ_n` on `C^{D_n} ⊇ C^{d_n}` with
`lim_ω D_n/d_n = 1` (resp. `D_n = d_n`) and `lim_ω ||σ_n(g) − P_n ρ_n(g) P_n||_2 = 0`
for every `g`. Here `P_n` projects onto `C^{d_n}` and `||·||_2` is normalized by `d_n`.

## Use for the hyperbolic Kazhdan premise

For `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`:
- **Amenable-trace mechanisms certify nothing beyond (T).** These are Hadwin--Shulman's
  character criterion, Dogon--Vigdorovich's `thm:HS_for_non_amenable_grps`, and
  uniqueness of embeddings of amenable algebras.
- **An instability witness can be taken properly non-amenable.** So a stability proof
  has to produce genuine representations on non-amenable limits: `L(Γ)` for separating
  approximations, and the twisted sectors that Dogon--Vigdorovich's corner theorem uses.

The artifact records mechanism by mechanism where each published stability tool stops.

## Credit

- **(A1) for extremal characters** is Dogon--Vigdorovich Lemma `lem:T CE implies rigidity`,
  combined with their Corollary `cor:eq defs of robust` ((T) implies (T;CE)).
- **(A2)** then follows from their Theorem `thm:HS_for_non_amenable_grps`.
- **The atomic decomposition for non-extremal traces, and the mixed reduction (A3),**
  were not found in the sources read. They are elementary, and no priority is claimed.

DERIVATION
kazhdan-properly-nonamenable-reduction-proof
