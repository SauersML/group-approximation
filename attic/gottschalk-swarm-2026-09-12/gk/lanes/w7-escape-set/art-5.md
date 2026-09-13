
## 5. Where it stops

**Proved here, on paper.**
- `S4` escapes conjugation into every weighted unit group, and `x_0` escapes by local finiteness (Section 1).
- `<S4>` sits in `EL_2(J_(F_3))`, contains `z`, and has a weakly finite symbol model with `z -> -1`. Every
  five-transvection set `S4 ∪ {T}` has a character model (Sections 2 and 3).
- Algebra-level models kill `D` (Lemma 3.1).
- Sofic subgroups containing `z` and the standard frame, in particular `H^ω_≤` with `ω(0) <= ω(1)`, have weakly
  finite models with `z -> -1` and `D != 0`; the tensor cube gives one explicitly (Section 4).

**Open.**
1. **Γ_5 and the defect** (`four-transvections-and-x23-force-defect-vanishing`). Every homomorphism
   `ρ : Γ_5 -> W^x` into a weakly finite `F_3`-algebra with `ρ(z) = -1` has `D_ρ = 0`.
   - **Why it is a candidate input.** With `weakly-finite-leavitt-representations-killing-defect-are-trivial` it gives
     `ternary-anti-central-summand-has-no-weakly-finite-image`. A unital `ψ : S_- -> W` with `W != 0` weakly finite
     gives `ρ(g) = ψ(ε_- g)` on `G` with `ρ(z) = -1`. Its restriction to `Γ_5` has `D = 0`, so `ρ` is trivial, so
     `-1 = 1` in `W` and `W = 0`.
   - **What it forces on Γ_5.** `Γ_5` is not sofic (Theorem 4.1), and no finite quotient of `Γ_5` separates the eight
     elements `z^e x_23(1)^a x_12(1)^b` with `e, a, b in {0,1}`.
   - **What is already firewalled.** Form (iii) on `Γ_5`. Every algebra-level model and each of its tensor powers kills
     `N_23`, and so does every model through `Γ_5 -> SL_2(F_3[ζ, ζ^(-1)])` (Corollary 3.4).
   - **What refutes it.** Soficity of `Γ_5`; a finite quotient separating those eight elements; any weakly finite
     model with `z -> -1` and `D != 0`.
2. **Soficity of <S4>.** `<S4>` is locally finite by linear
   (`jacobson-elementary-subgroups-are-locally-finite-by-linear`). Amenable-by-sofic is not known to be sofic; this
   is the same shape as `w7-el3j-sofic` (`research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md`). LEF and
   residual finiteness are not decided.
   - `<S4>` maps onto `SL_2(F_3[ζ, ζ^(-1)])`, which is finitely generated, linear and not virtually solvable. By the
     Tits alternative it contains a free group.
   - So `<S4>` is not amenable and lies in no amenable subgroup of `G`. Over `F_2` the same argument, with image
     `SL_2(F_2[ζ, ζ^(-1)])`, keeps it out of the amenable groups `U_< ⋊ P` of
     `lex-decreasing-units-with-order-preserving-letters-are-amenable`.
   - `graphs-of-locally-finite-groups-carry-regular-rank-models` needs a splitting of `<S4>` or `Γ_5` as a graph of
     locally finite groups, and none is known. Such a splitting would make the group sofic (sofic vertex groups,
     amenable edge groups), so for `Γ_5` this firewall is one case of the soficity refuter in item 1.
3. **<S6> and G.** `A(<S6>) = R`, so no algebra-level firewall applies to `<S6>` or to any group containing it.
   Whether `<S6> = G` is not decided.
4. **Other frames.** Whether a conjugate frame lies in `<S4>` is not decided (Proposition 3.2(c)). Five-transvection
   sets other than `Γ_5` do not contain the standard frame and are not classified for form (iv).

**Peer lanes (wave 7).**
- `w7-sub-multiletter` (37bafd8f3) landed `split-cylinder-data-cannot-force-defect-submultiplicativity` and
  `lex-decreasing-units-with-order-preserving-letters-are-amenable`. Both are rank-function statements about cylinder
  copies with swaps, and about `U_< ⋊ P`. `S4` has no swap letters, and it maps onto a nonamenable group. Nothing here
  repeats them.
- `w7-v-cycle-c3` (2e8bf4f44) landed `p-cycle-tree-invariance-cannot-force-order-char-law`, which is about rank models
  on `V`. There is no overlap.
- `w7-k2-unstable` has no claim node on main at c609c3bab, only the plan note 73770d983. There is no overlap.

**Nodes.**
- `four-transvection-set-escapes-depth-monotone-units` (Section 1), route `four-transvection-escape-proof`.
- `four-transvection-units-have-a-weakly-finite-symbol-image` (Sections 2 and 3), route
  `four-transvection-symbol-firewall-proof`.
- `depth-monotone-units-carry-weakly-finite-nonzero-defect` (Section 4), route `depth-monotone-tensor-cube-defect-proof`.
- `four-transvections-and-x23-force-defect-vanishing` (OPEN), route `summand-obstruction-from-four-transvection-defect`
  into `ternary-anti-central-summand-has-no-weakly-finite-image`.
