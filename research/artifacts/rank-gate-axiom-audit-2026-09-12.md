# Axiom audit of the rank gate: what each result consumes

Lane `w4-upg-audit` (family UPG), 2026-09-12. Supports:
- `regular-rank-ring-compressors-conserve-fixed-right-ideals` (established on paper, Section 2);
- `corner-defect-killing-rank-functions-are-augmentation` (established on paper, Section 1);
- later sections: the defect chain in regular rank rings, and the bare Sylvester defect gap.

Verification requested from `w4-vf-gate`.

Cited:
- [SYL] = `research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md` (lane `w4-rankfn`);
- [CH3] = `research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`, abstract-scope
  section (lane `w3-gate-char3`, 1bace02f7);
- [DI] = `research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md`;
- [TRI] = `research/artifacts/el3-two-root-identities-2026-09-12.md`;
- [RR] = `research/artifacts/el3-rank-ring-rigidity-2026-09-12.md`;
- [DG] = `research/artifacts/two-root-defect-descent-gap-2026-09-12.md`;
- [DP] = `research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md`;
- [RC] = `research/artifacts/rank-row-compression-audit-2026-09-12.md`.

## 0. Why the audit, and the three classes

The state upgrade (`ternary-anti-central-states-force-nontrivial-rank-models`) has two steps: (U1) a
state on `K_0(S_-)` gives a Sylvester matrix rank function on `S_-`, and (U2) a rank function gives a
matrix rank model. (U2) is unnecessary for every gate result whose proof survives in the abstract
setting. So each result is sorted by what it consumes.

- **(A) Sylvester axioms.** The proof works in any unital ring `B` with a Sylvester matrix rank
  function, faithful on elements where needed. Every Sylvester rank function `rk` on `K[Γ]` gives such
  a `B = K[Γ]/I_rk` ([SYL] Theorem 1, step 1).
- **(A') Regular rank rings.** The proof needs `B` von Neumann regular with a faithful rank function:
  principal right ideals, range and kernel idempotents, and the dimension calculus of [DG] Fact 1.1
  (Goodearl, *Von Neumann Regular Rings*, Chapter 16, imported at statement level as [DG] does).
  Rank ultraproducts are such rings; Lemma 2.1 shows the class is closed under corners and metric
  ultraproducts.
- **(B) Matrix structure.** Eigenvalues, Jordan forms and Kronecker products at finite level, rounding
  of almost-representations, transvection displacement in `GL_m`, or dimension counting of exact
  finite-level subspaces.

Results in (A) hold in (A'), and results in (A') hold for rank ultraproducts.

## 1. Classification

**Family R and the binary two-root gate.**

| node | class | load-bearing step; who scoped it |
|---|---|---|
| `el3-unit-root-matrix-units-iff-two-root-identities` | A | ring algebra, any rings ([TRI], [SYL] Cor. 5) |
| `reversed-root-pair-identity-forces-root-squares-to-vanish` | A | Weyl spread and commutator identities in any ring (its route) |
| [RR] Propositions 6, 8 and Corollary 9 | A | stated for rank ultraproducts, proofs are ring algebra ([SYL] Thm 1 step 3) |
| `matrix-unit-rank-models-extract-ring-rank-models` | A after replacement | Fitting lifting (B) only identifies the corner as an ultraproduct; replaced by the renormalized corner rank ([SYL] Thm 1 step 4) |
| `leavitt-algebra-has-no-unital-rank-model` | A after replacement | its step 1 counts kernels over fields (B); [DI] 2.1 gives "R has no Sylvester rank function" |
| `leavitt-rank-functions-killing-two-root-defect-are-augmentation` | A | [SYL] |
| `two-root-identity-is-corner-local-for-leavitt-rank-models` | A | Proposition 1.1 below |
| `toeplitz-isometry-defects-have-total-rank-at-least-one` | A | three axioms (its route) |
| `rank-ultraproduct-compressors-conserve-fixed-right-ideals`, degree `(1,0)` | A' | finite-level exact kernels (B) replaced by the dimension calculus (Theorem 2.2) |
| the same claim, degrees `(a,b) != (1,0)` | B | tensor powers at scale `n^(a+b)`; not consumed by the defect chain |
| `leavitt-rank-models-kazhdan-fixed-ideals-are-global`, degree `(1,0)` | A' | Corollary 2.4 |
| `leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model` | A' | invariant idempotent `q` with `qM = PM`, fixed ideal `fM` (Section 3) |
| `leavitt-rank-model-defect-gap-on-fixed-point-free-quotients` | A' | [DG] Fact 1.1 and a compactness step (Section 3) |
| `nested-two-root-defect-pieces-decay-geometrically-both-ways` | A' | [DG] Fact 1.1(c), globality on cylinders (Section 3) |
| `near-minimal-defect-models-have-multiplicative-cylinder-defects` | A' | [DG] Fact 1.1(d) (Section 3) |
| `transvection-displacement-forces-exact-local-embedding`, `rank-models-are-exact-representations-at-moving-finite-levels`, `natural-compressor-extension-fails-at-toeplitz-commutator` | B | level representations and rounding; construction-side normal forms, not consumed by any "No" argument |

**Characteristic three** (scope established by [CH3] and verified; recorded here for completeness).

| node | class | note |
|---|---|---|
| `ternary-leavitt-rank-models-move-z-iff-nontrivial` | A, except the PG transfer | the tensor-square lemma uses Kronecker products and Jordan forms (B) |
| `anti-central-rank-models-see-haar-measure-on-signed-diagonal` | A | rank positive on nonzero idempotents |
| `ternary-rank-model-root-element-torus-normal-form` | A | ring algebra plus the Haar law |
| `anti-central-rank-models-kill-ternary-corner-witnesses` | A | normalized idempotent rank is a state |
| `char-three-level-factoring-models-of-leavitt-units-are-trivial` | B | construction side |

**Dichotomy.** `simple-group-rank-functions-are-augmentation-or-detecting` and
`full-averaging-idempotent-kills-its-element-in-rank-models` are (A).

**Summary.** Every result consumed by a "No" argument is in (A) or (A'). The (B) steps are: tensor
degrees other than `(1,0)` in fixed-ideal conservation, the transfer from `G_3` to `PG`, and the
construction-side level normal forms. None of them is used by the defect chain or by the UPG route,
where `z` already acts by `-1` on `S_-`.

**Proposition 1.1 (corner locality for Sylvester rank functions).** Let `R = L_(F_2)(1,2)`, identify
`R^x = EL_3(R)` as in [SYL] Section 0, and let `D = N_23 N_12` in `F_2[R^x]`. For a proper prefix `P`
put `iota_P(g) = S[P] g T[P] + (1 - S[P]T[P])`. If a Sylvester matrix rank function `rk` on `F_2[R^x]`
has `rk(iota_P(D)) = 0`, then `rk` is the augmentation rank.

*Proof.* `T[P]S[P] = 1`, so `iota_P` is an injective group endomorphism of `R^x`, and its linear
extension is a unital ring endomorphism of `F_2[R^x]`. So `rk o iota_P` is a Sylvester matrix rank
function, and it kills `D`. By [SYL] Theorem 1 it is `rk_eps`: `rk(1 - [iota_P(g)]) = 0` for every `g`.
So `iota_P(R^x)` lies in `N_rk`, which is normal ([DI] Theorem 1.1). `R^x` is simple and
`iota_P(R^x) != 1`, so `N_rk = R^x`, and [DI] Theorem 1.1(3) gives `rk = rk_eps`. QED

For a homomorphism `sigma : R^x -> U^x` into a ring with a faithful rank function, pull `rk_U` back
along the linear extension of `sigma`. A vanishing corner product at `P` makes every `sigma(g) - 1` rank
zero, hence zero. That is `two-root-identity-is-corner-local-for-leavitt-rank-models` in class (A).

## 2. Fixed right ideals in regular rank rings

Setting: `U` is a unital von Neumann regular ring with a faithful Sylvester matrix rank function `rk`,
`rk(1) = 1`. For principal right ideals `rk(xU) := rk(x)` is well defined, and [DG] Fact 1.1(a),(b),(d)
hold: right annihilators are principal of rank `1 - rk(x)`, principal right ideals form a lattice on
which `rk` is a modular dimension function, and `rk(xJ) = rk(J) - rk(K)` for `J` principal containing
the right annihilator `K` of `x`.

**Lemma 2.1 (the class is closed).**
1. For a nonzero idempotent `e`, `eUe` is regular and `rk / rk(e)` is a faithful rank function on it.
2. Let `U_n` be regular rings with faithful rank functions and `omega` an ultrafilter. In `prod U_n`,
   `rk_omega(x) = lim_omega rk_n(x_n)` (entrywise on matrices) is a Sylvester matrix rank function, its
   null set `I` is a two-sided ideal, and `prod U_n / I` is regular with a faithful rank function.

*Proof.* 1. If `x = xyx` with `x` in `eUe`, then `x = x(eye)x`. The axioms restrict to matrices over
`eUe`, and faithfulness is inherited. 2. Products and quotients of regular rings are regular. The
Sylvester axioms are closed under pointwise limits. The null set of a Sylvester rank function is a
two-sided ideal, and the rank descends to the quotient faithfully ([DI] Remark 1.2). QED

**Theorem 2.2 (conservation, degree `(1,0)`).** Let `Gamma = <S>` be finitely generated, let `G` be
generated by elements of `P_Gamma = { g : g Gamma g^-1 <= Gamma }`, and let `sigma : G -> U^x` be a
homomorphism.
1. `Fix_r(sigma(Gamma)) = eU` for an idempotent `e`, and `rk((1-e)x) <= sum_(s in S) rk((sigma(s)-1)x)`
   for every `x` in `U`.
2. `sigma(G)` preserves `eU`, and every element of `<<Gamma>>_G` fixes `eU` pointwise. Hence
   `Fix_r(sigma(Gamma)) = Fix_r(sigma(<<Gamma>>_G))`.

*Proof.*
1. `Fix_r(sigma(Gamma))` is the intersection over `s` in `S` of `A_s = rann(sigma(s) - 1)`, which are
   principal. Finite intersections of principal right ideals are principal (Fact 1.1(b)), so it is
   `eU`. Fix `x` and put `J = xU`.
   - The right annihilator of `1 - e` is `eU`, and `xU + eU` is principal and contains it. By
     Fact 1.1(d) and modularity,
     `rk((1-e)x) = rk(xU + eU) - rk(eU) = rk(J) - rk(J cap eU)`.
   - The same computation with `sigma(s) - 1` gives `rk((sigma(s)-1)x) = rk(J) - rk(J cap A_s)`.
   - Modularity inside `J` gives `rk(I cap I') >= rk(I) + rk(I') - rk(J)` for principal `I, I' <= J`.
     Iterating over `S`, `rk(J cap eU) >= rk(J) - sum_s (rk(J) - rk(J cap A_s))`.
   Combining the three gives the bound.
2. Let `g` be in `P_Gamma`. Every element of `g Gamma g^-1` lies in `Gamma`, so
   `eU <= Fix_r(sigma(g Gamma g^-1)) = sigma(g) eU = (sigma(g) e sigma(g)^-1) U`. The two idempotents
   are conjugate, so the two principal right ideals have equal rank. `eU` is a direct summand of the
   larger one with a principal complement of rank `0`, which is `0` by faithfulness. So
   `sigma(g) eU = eU`, and `sigma(g)^-1 eU = eU`. These `g` generate `G`, so `sigma(G)` preserves `eU`.
   For `gamma` in `Gamma`, `g` in `G` and `y` in `eU`, `sigma(g)^-1 y` lies in `eU` and is fixed by
   `sigma(gamma)`, so `sigma(g gamma g^-1) y = y`. Products of conjugates fix `eU` pointwise. QED

**Remark 2.3.** No finite model and no ultraproduct is used. The `o(n_i)` dimensions of [RC] Section 1
become faithfulness. Degrees `(a,b) != (1,0)` need a tensor product of regular rank rings with a
multiplicative rank, which is not available in general; the defect chain never uses them.

**Corollary 2.4 (globality in regular rank rings).** Let `Gamma = EL_alpha(R)` be the nine-leaf
configuration. For every faithful regular rank ring `U` over any field and every homomorphism
`sigma : R^x -> U^x`, `Fix_r(sigma(Gamma)) = Fix_r(sigma(R^x))`.

*Proof.* As in `leavitt-rank-models-fixed-ideals-proof`, with Theorem 2.2 in place of the
rank-ultraproduct conservation claim. Its remaining inputs (the compressors generate `R^x`, and `R^x`
is simple) are group theory. QED
