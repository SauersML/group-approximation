---
rg: 2
id: houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
kind: claim
title: For n >= 2 the Houghton-like envelope H_n(E_nu(P)) has finitely presented germ group exactly when the near shift group R_nu is finitely presented, so generic enumerations of every infinite finitely presented input pass the germ gate
distinct_from:
  mz-envelope-fp-forces-two-sided-fg-near-index-kernel: that is the germ gate of the envelope E_nu(P) itself (n = 1), which needs R_nu finitely presented AND ker(eta) finitely generated; this shows that for H_n(E_nu(P)) with n >= 2 the two-sided window is not needed at all.
  shell-germ-fp-is-an-ascending-hnn-gate: that is the Cantor-shell germ gate (R_nu finitely presented plus a one-sided window); the germ gate here is R_nu finitely presented alone, strictly weaker than both.
  free-shift-shell-envelopes-are-not-finitely-presented: that kills the shell envelope for enumerations with R_nu = P*<s>; for the same enumerations this proves the Houghton-like germ group IS finitely presented.
  mz-envelope-germ-group-is-an-antitwisted-fiber-product: that computes E_nu(P)/FSym; this computes H_n(G)/FSym for every strongly shift-similar G and every n, and specializes it.
---

**ESTABLISHED** by `houghton-like-germ-groups-are-index-zero-products-proof`. This is a lane proof, not
independently reviewed. Its inputs are elementary, plus two Σ-invariant imports already on main.

**Setting.**
- `G <= Sym(N)` is an infinite strongly shift-similar group (Mallery--Zaremsky Definition 3.17), and
  `Germs(G) = G/FSym(N)` sits in `NearSym(N)`.
- `s̄` is the near class of `n -> n+1`, and `eta : NearSym(N) -> Z` is the near index, with `eta(s̄) = 1`.
- Put `Ĝ = <Germs(G), s̄> <= NearSym(N)`.
- For `n >= 1` put `Q_n(Ĝ) = { (x_1, ..., x_n) in Ĝ^n : eta(x_1) + ... + eta(x_n) = 0 }`.
- `H_n(G)` is the Houghton-like group of `houghton-like-groups-are-strongly-shift-similar`.

**Statement.**

1. **Germ groups.** `Ĝ = Germs(G) ⋊ <s̄>`. Recording the germ of an element on each ray `{k} x N` gives an
   isomorphism
   `H_n(G) / FSym([n] x N) ≅ Q_n(Ĝ)`.
2. **General gate.** For `n >= 3`, `H_n(G)/FSym([n] x N)` is finitely presented if and only if `Ĝ` is. For
   `n >= 2`, "only if" still holds.
3. **Mallery--Zaremsky envelopes.** Let `P` be infinite and finitely generated, `nu : P -> N` a bijection,
   `E_nu(P)` the envelope, and `R_nu = <lambda(P), s>` its near shift group, as in
   `mz-envelope-germ-group-is-an-antitwisted-fiber-product`. Then `Ĝ ≅ (R_nu x R_nu) ⋊ C_2 = R_nu wr C_2`.
   So for every `n >= 2`:
   `H_n(E_nu(P)) / FSym  finitely presented  <=>  R_nu finitely presented.`
4. **Necessity.** If `H_n(E_nu(P))` is finitely presented for some `n >= 1`, then `R_nu` is finitely presented.
5. **Generic enumerations pass.** Let `P` be infinite and finitely presented. By
   `regular-enumerations-can-make-near-shift-free-product`, a comeagre set of `nu` (computable ones if `P` has
   solvable word problem) have `R_nu ≅ P * Z`, which is finitely presented. For these `nu` and every `n >= 2`,
   the germ group of `H_n(E_nu(P))` is finitely presented. This holds although `E_nu(P)` itself is NOT
   finitely presented (`mz-envelope-fp-forces-two-sided-fg-near-index-kernel`, consequence 3), and neither is
   the Cantor shell envelope (`free-shift-shell-envelopes-are-not-finitely-presented`).

**Calibrations.**
- **`n = 1`.** Here `H_1(G) = G` (Mallery--Zaremsky Proposition 5.3), and item 1 gives `Q_1(Ĝ) = Germs(G)`. For
  `G = E_nu(P)` this contains `F^- = ker(eta + eta)` on `R x R` with index 2. That is exactly the two-sided gate
  of `mz-envelope-fp-forces-two-sided-fg-near-index-kernel`. Nothing new happens at `n = 1`. The gain comes from
  having at least three factors.
- **`G = FSym(N)`.** This is infinite and strongly shift-similar, with `Ĝ = <s̄> = Z` and `Q_n = Z^(n-1)`. That
  is the germ group of the Houghton group `H_n = H_n(FSym)`.
- **`G = H_k`.** Here `H_n(H_k) ≅ H_(nk)` (Mallery--Zaremsky Proposition 5.5). Items 1–2 give a finitely
  presented germ group `Z^(nk-1)`, as expected.

**What this changes.** For the Houghton-like envelope, the germ-level gate for Boone--Higman is just "some `nu`
makes `R_nu` finitely presented". Generic enumerations already achieve this for every infinite finitely
presented input. The two-sided window of the Mallery--Zaremsky compiler and the one-sided window of the shell
route are not needed. What remains is the passage from the germ group to `H_n(G)` itself:
`houghton-like-envelopes-lift-finite-presentation-from-germs` (OPEN). The route
`boone-higman-via-houghton-like-shift-envelopes` records what that would give. No lifting is claimed here.
