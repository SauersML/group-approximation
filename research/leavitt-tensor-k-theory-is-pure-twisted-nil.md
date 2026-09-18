---
rg: 2
id: leavitt-tensor-k-theory-is-pure-twisted-nil
kind: claim
title: For every unital ring A, A ⊗ L_2 has contractible homotopy K-theory, its K-theory is exactly two twisted Nil terms, and K_n-regularity of A ⊗ L_2 kills K_q for q <= n
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that needs A regular supercoherent and concludes K_*(L_2 ⊗ A) = 0; this has no hypothesis on A, concludes KH_*(A ⊗ L_2) = 0, and identifies K(A ⊗ L_2) with the twisted Nil terms that the regularity hypothesis is used to kill.
  regular-coherent-coefficients-kill-leavitt-tensor-k-theory: that needs A regular coherent and gives K_n = 0 for n >= 1; this is hypothesis-free and isolates what regularity is needed for.
  abc-leavitt-path-k-theory-exact-sequence: that imports the 1 - N^t sequence for regular supercoherent coefficients (ABC Theorem 7.6); this imports ABC Theorem 5.10 (arbitrary H'-unital coefficients, with Nil terms kept) and Theorem 8.6 (KH, arbitrary coefficients) and specialises both to the rose with two petals.
  leavitt-tensor-k1-sees-traces-of-nilpotent-matrices: that detects nonzero K_1(A ⊗ L_2) for special non-reduced A; this explains why any such class must live in the twisted Nil summands.
---

**ESTABLISHED (literature import, specialisation checked here).** Route:
`abc-leavitt-kh-vanishing-and-nil-splitting-citation`.

Let `L = L_Z(1,2)`, the Leavitt path algebra of the rose `R_2` (one vertex, two
loops). Let `A` be any unital ring, and write `L_A = A ⊗_Z L`. When `A` is an
`F_2`-algebra, `L_A = A ⊗_(F_2) L_(F_2)(1,2)`, because
`L_(F_2)(1,2) = L ⊗_Z F_2`. Then:

1. **(KH vanishes.)** `KH(L_A)` is contractible, so `KH_n(A ⊗ L) = 0` for all
   `n ∈ Z`.
2. **(K is pure Nil.)** Let `U_A = L_0 ⊗ A`, where
   `L_0 = colim_n M_(2^n)(Z)` is the degree-zero part of `L`. Let `φ` be the
   corner isomorphism `x -> t_+ x t_-`. Then there is an equivalence of
   nonconnective spectra
   ```text
   K(A ⊗ L)  ≅  NK(U_A, φ⊗1)_+  ⊕  NK(U_A, φ⊗1)_- .
   ```
3. **(Regularity suffices.)** If `A ⊗ L` is `K_n`-regular, then
   `K_q(A ⊗ L) = 0` for every `q <= n`.
4. **(Exact form of the Leavitt K-condition.)** For every `F_2`-algebra `B`,
   ```text
   K_1(B ⊗ L) = K_2(B ⊗ L) = 0
     ⟺  NK_q(U_B, φ⊗1)_± = 0  for q = 1, 2.
   ```

## Proof from the imports

All quotations are from the citation route. They were read on 2026-09-18 from
the arXiv HTML of arXiv:0903.0056.

**(1).** Apply ABC Theorem 8.6 to the quiver `E = R_2`. The quiver has one
vertex `v` and two arrows `v -> v`.
- `E` is finite, so it is row-finite, and `Sink(E) = ∅`.
- The adjacency matrix is `N'_E = (2)`, since `n_vv = #{arrows v -> v} = 2`.
- Removing the sink columns removes nothing, so `N_E^t = (2)` and `1 = (1)`.

Theorem 8.6 gives
`KH(L_A(E)) ≅ hocofiber(KH(A) --(1-2)--> KH(A))`. The map `1 - 2 = -1` is
multiplication by `-1`, an equivalence of spectra, so its homotopy cofiber is
contractible.

ABC use `L_A(E) = L_Z(E) ⊗ A` as the definition of `L_A(E)`. So `L_A(E)` is
exactly `A ⊗ L`.

**(2).** Apply ABC Theorem 5.10 with the same `E`. Its hypotheses hold:
- a unital ring is H'-unital;
- `E` is finite;
- `E` has no sources, since `v` receives an arrow.

The theorem gives
`K(L_A(E)) ≅ NK(L_0⊗A, φ⊗1)_+ ⊕ NK(L_0⊗A, φ⊗1)_- ⊕ hocofiber(K(A)^(e_0 - e_0') --(1-N^t)--> K(A)^(e_0))`.

Here `e_0 = 1` (vertices) and `e_0' = 0` (sinks), and `1 - N^t = -1` as in (1).
So the last summand is contractible.

ABC describe `L_0 = ⋃_n L_(0,n)` with
`L_(0,n) ≅ [∏_(m<n) ∏_(i ∈ Sink(E)) M_|P(m,i)|(Z)] × [∏_(i ∈ E_0) M_|P(n,i)|(Z)]`.
With no sinks and one vertex, `|P(n,v)| = 2^n`, since there are two choices of
arrow at each of `n` steps. So `L_(0,n) = M_(2^n)(Z)`.

**(3).** ABC Section 8, citing Weibel [32]: "if A is unital and
K_n(A)→K_n(A[t_1,…,t_p]) is an isomorphism for all p≥1, (i.e. A is
K_n-regular) then (8.1) is an isomorphism for ∗≤n". The map (8.1) is
`K_*(A) -> KH_*(A)`.

Apply this to the unital ring `A ⊗ L`. Its `KH` vanishes by (1), applied to the
same `A`.

**(4).** This follows from (2) on homotopy groups, applied to `A = B`. ∎

## Consequences for the graph

- **No homotopy-invariant obstruction.** For every group `Λ` and every action
  on a compact zero-dimensional `X`, free or not, `B = LC(X,F_2) ⋊ Λ` has
  `KH_*(B ⊗ L) = 0`. No Farrell-Jones hypothesis is needed for this.
  - An obstruction to `free-action-leavitt-tensor-hosts-have-trivial-k1-k2` can
    therefore never be seen by a homotopy-invariant, excisive theory.
  - Such theories include KH itself, KH-assembly, and any invariant that
    factors through KH.
  - The obstruction must live in the twisted Nil summands of (2).
- **The trivial Z/2 action.** The `K_1 ≠ 0` found by
  `leavitt-tensor-k1-sees-traces-of-nilpotent-matrices` is such a Nil class.
  In particular, `LC(X,F_2)[Z/2] ⊗ L` is not `K_1`-regular.
- **Where Farrell-Jones is still needed.** In the Farrell-Jones argument for
  `cantor-crossed-product-leavitt-tensors-are-k-trivial`, the part that
  genuinely needs group hypotheses is only the vanishing of these Nil terms.
