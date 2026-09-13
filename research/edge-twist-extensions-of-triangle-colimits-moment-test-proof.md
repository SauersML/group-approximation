---
rg: 2
id: edge-twist-extensions-of-triangle-colimits-moment-test-proof
kind: route
title: Lift the free Q-set to a C-torsor over it; cocycles are coboundaries, and the obstruction is one affine intersection
target: edge-twist-extensions-of-triangle-colimits-moment-test
requires: [finite-central-extension-rf-iff-virtually-splits, hyperbolic-rf-question-equals-vtf-question]
---

Notation as in the claim. `π : Λ -> Q` is the quotient map, and it is injective on every
vertex group because `N` is torsion-free. `M = F_p^Q`, with `(g·w)(q) = w(π(g)^{-1} q)`,
and `1 in M` denotes the constant function.

**(M1).** `T_c` is a simple complex of groups, since both composites face -> vertex send
`z ↦ (1,z)`. `C` acts trivially on the cosets, so its links are the coset graphs of `T`.
So it is nonpositively curved, hence developable (Bridson–Haefliger III.C.4.17), and `C`
injects. `C` is central and killing it gives `Λ`. A finite central extension of a
hyperbolic group is hyperbolic.

**(M2), lifts as cocycles.** A homomorphism `φ : Λ_c -> M ⋊ Q` over `π`, with `C ↦`
constants, is the same thing as homomorphisms `φ_v : A_v × C -> M ⋊ Q` agreeing on the
edge groups. Write `φ_v(a, z) = (f_v(a) + z·1, π(a))`.
- This is a homomorphism iff `f_v` is a 1-cocycle `A_v -> M`, because `π(a)·1 = 1`.
- The edge condition at `e = ij` compares `(x,z)` in `A_i × C` with `(x, z + c_e(x))` in
  `A_j × C`, and reads `f_i(x) = f_j(x) + c_e(x)·1` for `x in E_e`.

`M` is a free `F_p[A_v]`-module, since `A_v` acts freely on `Q`. So `H^1(A_v; M) = 0`
and `f_v(a) = (a-1) u_v` for some `u_v in M`. Put `w_e = u_i - u_j`. Then:
- `(x - 1) w_e = c_e(x)·1` for `x in E_e`;
- `w_13 = w_12 + w_23`.
Conversely, given `w_e` with these properties, `u_3 = 0`, `u_2 = w_23`, `u_1 = w_13`
reconstruct the `f_v` and hence `φ`.

**(M2), the affine intersection.** Let `S_e = {w : (x-1)w = c_e(x)·1 for x in E_e}`.
- Along a right coset `{x_e^k q_0}` set `w_e^0(x_e^k q_0) = -k c_e(x_e)`. This is
  well-defined mod `p` and lies in `S_e`, so `S_e = w_e^0 + M^{E_e}`. Here `M^{E_e}` is
  the space of functions constant on right cosets.
- A lift exists iff `w_13^0 - w_12^0 - w_23^0` lies in `M^{E_12} + M^{E_13} + M^{E_23}`.
- Using the pairing `<λ, w> = Σ_q λ(q) w(q)`, the annihilator of that sum is exactly
  `Z_N`. And `<λ, w_e^0> = -c_e μ_e(λ)`, where `c_e` also denotes `c_e(x_e)`.
So a lift exists iff `c_13 μ_13(λ) - c_12 μ_12(λ) - c_23 μ_23(λ) = 0` for all `λ in Z_N`.

Changing the base point `q_0` to `x_e q_0` changes `μ_e` by `Σ_coset λ = 0`, so `μ_e` is
well-defined. The image of such a `φ` is finite and injective on `C`.

**(M3).** One direction is (M2).

For the converse, let `ρ : Λ_c -> R` be finite and injective on `C`.
- `ker ρ` meets `C` trivially, so it maps isomorphically onto a finite-index normal
  `H_0` of `Λ`.
- Let `N_1` be torsion-free normal of finite index, and `N = H_0 ∩ N_1`. Its preimage
  intersected with `ker ρ` is a normal complement `s(N)` of `C` over `N`. So
  `Q_c = Λ_c / s(N)` is a central extension of `Q` by `C`.
- `Λ_c` acts on `Q_c` by left multiplication, commuting with the free translation action
  of `C`. So it lands in the centralizer of that action, `C^Q ⋊ Sym(Q)`, with `C ↦`
  constants and `Sym(Q)`-part `π`. This is a lift, and (M2) applies to `N`.

**(M4).** Let `N' <= N`, both torsion-free normal, with `Q' -> Q` onto. Put
`push(λ')(q) = Σ_{q' ↦ q} λ'(q')`.
- `E_e` injects into `Q` and `Q'`, so right cosets `E_e q'` map bijectively onto
  `E_e q`. Hence `push(Z_{N'}) <= Z_N`.
- Choosing base points in `Q'` over those in `Q` gives `μ_e(λ') = μ_e(push λ')`, so
  `I_{N'} <= I_N`.
- Any two such `N` contain a third, so these subspaces of `F_p^3` stabilize at some
  `I_∞`.
By (M2)–(M3), `c` splits virtually iff `<c, I_N> = 0` for some `N`, iff `<c, I_∞> = 0`.

**(M5).** Let `N' <= N` have index prime to `p`. The transfer
`tr(λ)(q') = λ(image of q')` maps `Z_N -> Z_{N'}`, and `push ∘ tr = [N:N']·id`, which
is invertible mod `p`. So `push` is onto `Z_N` and `I_{N'} = I_N`.

**(M6).** Suppose `I_∞ != 0` and choose `c` with `<c, I_∞> != 0`.
- If `Λ` is residually finite, `Λ_c` has no finite quotient injective on `C`. It is not
  residually finite (`finite-central-extension-rf-iff-virtually-splits`), and it is
  hyperbolic by (M1).
- If `Λ` is not residually finite, `Λ` itself is the example.
A torsion-free normal `N` is available because `Λ` is assumed virtually torsion-free.
Without that assumption, `hyperbolic-rf-question-equals-vtf-question` gives a
non-residually-finite hyperbolic group anyway.
