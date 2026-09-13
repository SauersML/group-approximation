# Weakly finite hosts for Leavitt unit groups: construction-side census

Lane `w6-wf-construct`, 2026-09-12. This is the construction side of the weak-finiteness form of both
counterexample routes. The task was to build a nontrivial homomorphism `ρ : G -> W^x`, with `W` a weakly
finite ring of characteristic `p`, for one of:
- `G = L_(F_2)(1,2)^x` (`p = 2`);
- `G = G_3 = L_(F_3)(1,2)^x` with `ρ(z) = -1` (`p = 3`).

Such a `ρ` refutes `binary-complement-corner-has-no-weakly-finite-image` (through
`binary-corner-weakly-finite-images-are-unit-representations`) or
`ternary-leavitt-units-have-no-weakly-finite-representation`, respectively.

"Weakly finite" means: for every `n`, `AB = I_n` implies `BA = I_n` in `M_n(W)`.

## 0. Result

No construction. Two theorems, two propositions and one open sufficient target:
- **Theorem A** (`leavitt-unit-hosts-need-nilpotents-of-unbounded-index`): every host, weakly finite or not,
  contains nilpotents of unbounded index. One argument kills division rings, matrices over division rings,
  semisimple Artinian and prime Goldie rings, reduced rings and finite-dimensional algebras.
- **Theorem B** (`leavitt-unit-hosts-exclude-matrices-over-commutative-rings`): no nontrivial host inside
  `GL_n(C)` with `C` commutative, whatever the nilpotents of `C`. It rests on Malcev's residual finiteness,
  imported at statement level.
- **Proposition C** (`char-p-traces-cannot-certify-stable-finiteness`): in characteristic `p` no trace certifies
  weak finiteness; only `K_0`-functionals with values of infinite order can.
- **Proposition D** (`weakly-finite-leavitt-hosts-reduce-to-bounded-matrix-size`): by Łoś, a host exists iff for
  every `n` there is one directly finite in matrix sizes `<= n`. So a proof that no host exists may fix a single
  matrix size `n_0`, uniform over all hosts.
- **Open** (`leavitt-unit-lifted-trace-detects-nonzero-idempotents`): a `p`-adic Kaplansky-type faithfulness of the
  lifted trace would make `F_p[G]` itself a host and refute both routes.

## 1. Theorem A: hosts need nilpotents of unbounded index

**Theorem A.** Let `p` be prime, `G = L_(F_p)(1,2)^x`, and `W` a nonzero ring with `p·1 = 0` whose nilpotent
elements all satisfy `x^N = 0` for one fixed `N`.
1. For `p = 2`, every homomorphism `ρ : G -> W^x` is trivial.
2. For `p = 3`, no homomorphism `ρ : G -> W^x` has `ρ(z) = -1`. This part uses one input: every normal subgroup
   of `G_3` lies in `{±1}` or equals `G_3`. That is simplicity of `G_3/{±1}` together with perfectness, the same
   input as `ternary-weakly-finite-representations-give-anti-central-images`.

The key step holds for every `ρ`: if `x ∈ G` has order `p^k` and `p^j >= N`, then `ρ(x)^(p^j) = 1`.

**Proof.**
- **p-power elements.**
  - For every `n >= 1` there is a complete prefix code `w_1, …, w_n`, for example `0, 10, 110, …, 1^(n-2)0, 1^(n-1)`.
  - For `π ∈ S_n`, `u_π = Σ_i s_(w_(π(i))) t_(w_i)` is a unit of `L_(F_p)(1,2)` with inverse `u_(π^(-1))`, because
    `t_w s_(w') = δ_(w,w')` on a prefix code and `Σ_i s_(w_i) t_(w_i) = 1`.
  - So `S_n ≤ V ≤ G` for every `n`, and `G` contains elements `x` of order exactly `p^k` for every `k`.
- **Unipotence in characteristic p.** The elements `1` and `ρ(x)` commute and `p·1 = 0`, so the binomial theorem
  gives `(ρ(x) - 1)^(p^k) = ρ(x)^(p^k) - 1 = 0`. So `ρ(x) - 1` is nilpotent, hence `(ρ(x) - 1)^N = 0`. For
  `p^j >= N` this gives `(ρ(x) - 1)^(p^j) = 0`, which by the same identity reads `ρ(x)^(p^j) = 1`.
- **Kernel.** Take `k = j + 1`. Then `y = x^(p^j)` has order `p`, so `y ≠ 1`, and `ρ(y) = 1`.
  - `p = 2`: `G` is simple (`binary-leavitt-unit-group-is-simple`), so `ker ρ = G`.
  - `p = 3`: `y` has order 3, so `y ∉ {±1}`. By the normal-subgroup input `ker ρ = G_3`, so `ρ(z) = 1`. But `1 ≠ -1`
    in a nonzero ring of characteristic 3. ∎

**Sharper form.** Suppose `ρ` is nontrivial, or for `p = 3` that `ρ(z) = -1`.
- Then `ker ρ` contains no element of order `p`, by the argument above.
- So for a `p^k`-cycle `x`, `(ρ(x) - 1)^(p^(k-1)) = ρ(x^(p^(k-1))) - 1 ≠ 0`.
- A host therefore contains the explicit nilpotents `ρ(x) - 1`, of index greater than `p^(k-1)`, for every `k`.

**Corollary A.1 (dead sources).** None of these rings receives a nontrivial `ρ`, and for `p = 3` none receives
one with `ρ(z) = -1`:
- **division rings** of characteristic `p`, where `N = 1`. This recovers item 4 of
  `research/artifacts/binary-weakly-finite-representations-2026-09-12.md`;
- **matrix rings `M_n(D)`** over a division ring `D`. A nilpotent endomorphism of the `n`-dimensional `D`-space
  `D^n` satisfies `x^n = 0`. The same holds for every subring of `∏_i M_(n_i)(D_i)` with all `n_i <= n`;
- **prime or semiprime right Goldie rings.** Their classical ring of quotients is semisimple Artinian (Goldie's
  theorem, at statement level, not re-read), so they are subrings of a finite product of matrix rings over
  division rings;
- **reduced rings**, where `N = 1`;
- **finite-dimensional algebras** of characteristic `p`. Left multiplication is faithful, so `x^(dim W) = 0`;
- **algebraic ultraproducts of matrix algebras of bounded size.**

**What is left.** A host must contain nilpotents of unbounded index. Rank ultraproducts
`∏_U M_(n_i)(K)/(rank-null ideal)` with `n_i -> ∞` have them, and linear soficity lives there. So do `F_p[G]`
itself and every ring containing it.

## 2. Theorem B: matrices over commutative rings

**Theorem B.** Let `C` be a nonzero commutative ring and `n >= 1`.
1. Every homomorphism `L_(F_2)(1,2)^x -> GL_n(C)` is trivial.
2. If `C` has characteristic 3, no homomorphism `G_3 -> GL_n(C)` sends `z` to `-1`. This uses the same
   normal-subgroup input as Theorem A(2).

**Proof.**
- **Finite generation.** `L_(F_2)(1,2)^x` is finitely presented (`leavitt-unit-group-finitely-presented`).
  `G_3 = ⟨V, x⟩` for one transvection `x` (`leavitt-prime-field-units-generated-by-v-and-one-transvection`), and
  `V` is finitely generated (`thompson-v-finitely-presented-infinite-simple`).
- **Malcev.** Every finitely generated subgroup of `GL_n(C)`, `C` commutative, is residually finite. This is
  imported at statement level and was not re-read.
- **So** `ρ(G)` is a residually finite quotient of `G`.
  - **`p = 2`:** `G` is infinite and simple, so `ρ(G)` is `1` or `≅ G`. An infinite simple group has no proper
    finite-index normal subgroup, so it is not residually finite. Hence `ρ(G) = 1`.
  - **`p = 3`:** by the normal-subgroup input, the quotients of `G_3` are `G_3`, `G_3/{±1}` and `1`. The first two
    are infinite with no proper finite-index normal subgroup, so they are not residually finite. Hence `ρ` is
    trivial and `ρ(z) = 1 ≠ -1`. ∎

**Scope.** Theorem B covers `M_n(C)` for non-reduced `C` of any nilpotence, where Theorem A says nothing. It also
covers products `∏_i M_n(C_i) = M_n(∏_i C_i)` at fixed `n`. Growing `n` is not covered.

**Remark B.2 (PI rings, conditional imports, no node).**
- **Semiprime PI rings** embed in matrices of bounded size over commutative rings (Posner–Rowen–Amitsur, statement
  level), so they die by Theorem B.
- **A general PI host `W`:**
  - the subalgebra generated by the finitely many `ρ(s^(±1))` is a finitely generated PI algebra;
  - its Jacobson radical `J` is nilpotent (Braun–Kemer–Razmyslov, statement level);
  - modulo `J` the image dies by Theorem B, so `ρ(G) ⊆ 1 + J`;
  - `1 + J` is a nilpotent group, and `G` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`), so `ρ` is trivial.
- So every PI host is dead, conditional on those imports.
