# ZP topology review, 2026-09-13, part 6

Reviewer lane: z-verify-topology. Verdict conventions as in part 1.

## 27. Problem 1.04, Leary's cofinite family (z1-04-fp-fh, abc96d92da): PASS

- **`isolated-type-fn-vertex-stabilizers-give-type-fhn` (Proposition V): PASS.**
  - **Building E_v.** For the connected free cocompact G_v-complex E ⊇ Lk_v, the regular covering
    E → E/G_v gives 1 → π₁E → π₁(E/G_v) → G_v → 1. Both π₁(E/G_v) (finite complex) and G_v are
    finitely presented, so π₁E is finitely normally generated. Finitely many orbits of 2-cells make E
    simply connected. Then Lemma S, FP_n and Hurewicz kill H₂,…,H_{n−1} with finitely many orbits of
    spherical cells.
  - **Replacement.** The mapping-cylinder replacement is free and cocompact.
  - **Homology.** In the map of Mayer–Vietoris sequences along ⊔Lk_v, the terms H_k(Lk), H_k(A),
    H_{k−1}(Lk) and H_{k−1}(A) are identities, and H_k(N_v) = H_k(pt) → H_k(E_v) is an isomorphism for
    k ≤ n−1. The five lemma gives H_k(Y) ≅ H_k(X) for k ≤ n−1.
- **`leary-gls-cocompact-slabs-with-isolated-stabilizers` (+ `-citation`): PASS on the quoted
  statements.** They were read from the TeX source, and I did not re-read them.
- **`leary-groups-with-cofinite-s-are-type-fhn` (Theorem L): PASS.**
  - For m ≥ max|ℤ−S| every branch height lies in the slab, so enlarging the slab only cones off copies
    of L. Hence H_i(X(m′), X(m)) = ⊕H̃_{i−1}(L) = 0 for i ≤ n.
  - Contractibility of the union then makes X(m) (n−1)-acyclic. Its only singular vertices carry
    π₁(L), which is finitely presented and FP_n, hence F_n, so Proposition V applies.
  - The scope statement is honest: this gives FH_n at each finite n over ℤ, not FH. Leary's question
    was about FH(R).

## 28. Problem 2.05, V obstruction (z2-05-v-dehn, b589d11a1f): PASS

**`thompson-v-elements-need-unboundedly-many-non-f-letters`.**
- (1) br = 1 on F, which preserves the lexicographic order; br(g⁻¹) = br(g).
- (2) br(gh) ≤ br(g) + br(h) − 1. Pieces I_j ∩ h⁻¹(J_t) are clopen, order-convex, gh is order-preserving
  on them, and their images are intervals. Their number is ≤ k + (l−1), because each of the l−1 cut
  positions is interior to at most one image h(I_j).
- (3) br(r_k) = 2^k. With fewer pieces, some piece meets two depth-k cones, and r_k reverses their order.
- (4) A word for r_k needs ≥ (2^k−1)/b_S non-F letters. (5) br ≤ 2 on T.
- It kills the bounded-non-F-letter normal-form route (correctly `invalidates`). V quadratic stays open.

## 29. Problem 2.04 fences (z2-04-f-qi, 484133d9de, 7982e36cea, a4d949a07f): five PASS

- **`amenability-is-a-quasi-isometry-invariant`: PASS.**
  - Fibres of a QI are bounded (≤ |B(2C)|).
  - The preimage A = f⁻¹(B) of a thick-boundary Følner set has |A| ≥ |B°|/K′. For y ∈ B° (distance
    > C from the complement), f(g(y)) ∈ B.
  - |∂_r A| ≤ K|∂_t B| because f maps ∂_r A into ∂_s B.
  - The resulting ratio bound is correct.
- **`thompson-t-is-not-amenable`: PASS.**
  - An invariant probability measure on S¹ has no atoms (orbits of dyadic rotations are infinite) and
    full support (orbits are dense).
  - h(x) = μ([0,x)) is a homeomorphism conjugating T into rotations, which would make T abelian.
- **`thompson-f-f-times-z-f-times-f-are-mutual-subgroups`: PASS.** F_[a,b] ≅ F, Stab(1/2) ≅ F×F, and
  F ⊇ Z^n, so asdim F = ∞.
- **`thompson-f-has-vanishing-zg-cohomology` (+ `-citation`, Brown–Geoghegan Thm 7.2): PASS on the
  quoted statement.**
- **`thompson-products-have-vanishing-zg-cohomology`: PASS.**
  - For finite-type free resolutions, Hom_{G×H}(P⊗Q, Z[G×H]) ≅ Hom_G(P,ZG) ⊗ Hom_H(Q,ZH), a tensor
    product of cochain complexes of free abelian groups.
  - Künneth, with all H^p of the first factor zero, gives vanishing.
- The reduction of part (c) to amenability of F and the two conditional routes are correct and do not
  fire.

## 30. Problem 1.06 dead-edge rings (z1-06-bns-artin, fc6baf3e4a, 2ac3d5fac3): four PASS

- **`artin-sigma1-dead-edge-ring-obstruction` (Theorem C): PASS.**
  - g ↦ t^{χ(g)}ρ(g) is a unit-valued homomorphism into S = R((t)), since t is central.
  - **Lemma A.** The map ZG → S extends to the Novikov completion. Σ¹ = −Σ¹ plus Sikorav make the free
    Novikov chain complex exact in degrees ≤ 1, which is split in degree 0, so H₁(G; M) = 0 for every
    Novikov module M.
  - **Fox derivatives.** Recomputed for r = (uv)^k(vu)^{−k}: ∂r/∂u = (1−v)S_k(uv) and
    ∂r/∂v = (u−1)S_k(vu). Correct.
  - **Φ(w) = Σ_{x∈V₁} w_x(X_x − 1) kills every relator row:**
    - edges inside V₁, by Fox's fundamental formula;
    - edges inside V₂, trivially;
    - cross dead edges, because X_uX_v = ρ(uv) when χ(u)+χ(v) = 0 and S_k(ρ(uv)) = 0 by hypothesis.
  - **Φ is onto S on ker ∂₁.** w_{v₁} = s(X_{v₁}−1)⁻¹ and w_{v₂} = −s(X_{v₂}−1)⁻¹, with live
    v_i ∈ V_i; t^nρ − 1 is invertible in R((t)) for n ≠ 0.
  - So H₁ ≠ 0 and ker χ is not finitely generated.
- **`artin-346-dead-character-outside-sigma1-by-rank-two-rep`: PASS.** I recomputed the matrices:
  - M y M = [[ω+1/2, ω−1], [(ω²−ω)/2, ω²/2+ω]], and −y M² y has the same entries (using ω² = −1−ω and
    ω³ = 1). So bcb = cbc holds.
  - ρ(ab) = −I, ρ(ac) = y, y³ = I, and I + y + y² = 0. M is invertible (det = −3ω/2).
  - The cut {a}|{b,c} has only dead cross edges.
- **`artin-346-commutative-rings-miss-the-dead-cut`: PASS.** (bc)b(bc)⁻¹ = c gives ρ(b) = ρ(c), and
  (1+z+z²) − z(1+z) = 1.
- **`artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring`: PASS.** The only admissible cut is
  {u₁,u₂}|{v₁,v₂}. From ū₁v̄₁ = −1 = ū₂v̄₁ we get ū₁ = ū₂, so S₃(−1) = 1.
- **Graph.** The two universal-witness claims carry `refuted_by` counterexamples, which imply their
  negations, and the dead routes requiring them stay open. Correct.
- The citation imports (Meier bounds, known families, Escartín-Ferrer) are plausible as quoted from
  arXiv:2501.08692v3; I did not re-read them.

## 31. Housekeeping

- z4-04 reports both §17 hygiene fixes at 1496a9146c:
  - `connected-rips-complexes-pass-to-direct-products-proof` now requires z4-06's product claim;
  - `group-rips-complexes-are-cayley-graph-flag-complexes` has a `distinct_from` naming z4-07's claim.
  I have not re-read that commit.
- Pending in my queue:
  - z4-01 8708abaf12. It lands `asymptotically-cat0-groups-have-contractible-rips`, which may duplicate
    z4-07's `torsion-free-asymptotically-cat0-groups-have-contractible-rips`; to check.
  - z4-05 3b6d8bee57 and 572598fa21 (Jensen–Helly abstraction, cographs).
  - z1-05 8814175312 and the direct-route landings.
  - z1-08 efee418676 / f1a1b6dee7 / ac3acde9d0.
  - z1-24, z1-16, z1-17, the 1.01 ffz-fpinf landings, 1.18 68481e4d7c, 1.09 58aef0a2bd.
  - z1-21-type-f-proof conditional routes, z1-19 part 1, 4.02 9bf6fcec5f.
