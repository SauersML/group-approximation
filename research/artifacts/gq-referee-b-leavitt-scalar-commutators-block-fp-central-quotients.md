# Referee report (citation/hypothesis lens): `leavitt-scalar-commutators-block-fp-central-quotients` and `leavitt-resolvent-derived-units-mod-centre-not-fp`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: both claims and their `-proof` routes, as landed at 90ff0b8ea.
Together they refute `leavitt-resolvent-derived-units-mod-centre-fp-simple`.

## Verdict

**PASS.** The refutation stands. It uses:
- one elementary group lemma, checked;
- two external theorems, both checked at source;
- the part of the `R_L` node already checked.

There is one repo-internal import, used only for the `E_N` bullet (A2).

## Checks

**Group lemma (part 0). Correct.**
- Choose `H_0` finitely generated with `H = H_0 C`.
- `[H,H] = [H_0,H_0] ≤ H_0`, since `C` is central, so `C_0 ≤ H_0 ∩ C`.
- `H_0/(H_0 ∩ C)` is finitely presented, so `H_0 ∩ C` is the normal closure of finitely many central elements.
  That makes it finitely generated abelian, and it contains the non-finitely-generated `C_0`, a contradiction.

**Part 1, the Leavitt copy.**
- `L_K(1,d) → R` is injective because `L_K(1,d)` is simple. This is verified at source, Ara–Goodearl–Pardo,
  *K₀ of purely infinite simple regular rings*, arXiv:math/0111066 (ar5iv), Theorem 4.2: "For every natural
  number n ≥ 2, V₁,ₙ is a purely infinite simple ring, and K₀(V₁,ₙ) ≅ ℤ/(n-1)ℤ", with `k` a field.
- `C_0` is central because `K ⊆ Z(R)`.

**Part 1, `C_0 ≤ [U_d, U_d]`.**
- AGP Theorem 2.4 (ar5iv), verbatim: "If R is a purely infinite simple ring then K₁(R) = U(R)^ab". The hypotheses
  match.
- Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*, arXiv:0903.0056 (ar5iv), Corollary 7.7: "Let k be a
  principal ideal domain and let E be a row-finite quiver. Then … K₁(L_k(E)) ≅ coker(1−N^t) ⊕ ker(1−N^t)."
  - The ar5iv rendering drops the coefficient groups. The repo node records them as `K_1(k)` and `ℤ`.
  - For the rose with `d` petals over a field this gives `K^×/(K^×)^{d−1}`.
  - For `d = 2`, the only case the refutation needs, it gives `K_1 = 0`, so `L_K(1,2)^×` is perfect. This matches
    part 1 of `leavitt-unit-groups-over-every-field-are-simple-mod-scalars`.
- The incidence-convention caution recorded in the ABC node is irrelevant here: for one vertex, `N^t = N = (d)`.

**Part 1, `C_0` not finitely generated. Correct in every case.**
- In characteristic 0, `K^×` contains the free abelian group on the primes.
- In characteristic `p`, either `K^×` is infinite torsion (algebraic case), or `K` contains `F_p(t)`, whose units
  contain the free abelian group on the monic irreducible polynomials.
- `μ_{d−1}(K)` is finite.

**Part 2, instances. Correct.**
- For `d = 2`: `U_2 = [U_2,U_2] ≤ [R^×,R^×]`, so `C_0 ≤ [H,H]` for `H = [R^×,R^×]`.
- The node correctly restricts the derived-subgroup bullet to `d = 2`.

**The refutation for `R_L`.**
- `Q ⊆ Z(R_L)` unitally: the `u_m` computation plus the `Q^(X)` model, checked in
  `gq-referee-b-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md` and now the claim
  `leavitt-resolvent-ring-is-fp-and-contains-q`.
- `s_i, t_i` form a Leavitt `(1,2)` family.
- `Q^× ≤ L_Q(1,2)^×`, and that group is perfect. So `L_Q(1,2)^× ≤ [U,U] = D`, and
  `Q^× ≤ [L_Q(1,2)^×, L_Q(1,2)^×] ≤ [D,D]`.
- `Q^×` is central, so `Q^× ≤ Z(D) ∩ [D,D]`. The lemma applies to `D`, to `U`, and to `E_N(R_L)`.
- `leavitt-resolvent-derived-units-mod-centre-fp-simple` asserts that `D/Z(D)` is finitely presented. **That
  assertion is refuted**, and the route `gl-n-q-bh-via-leavitt-resolvent-units` is dead.

## Amendments

- **A1.** Step 1 of `leavitt-resolvent-derived-units-mod-centre-not-fp-proof` cites part 1 of the full ring node.
  Re-point it at `leavitt-resolvent-ring-is-fp-and-contains-q`, so the refutation does not depend on the simplicity
  claim.
- **A2 (trust surface).** The `E_N(R_L)` bullet uses `GL_N(L_K(1,2)) = EL_N(L_K(1,2))` from
  `leavitt-gl-equals-el-and-perfect-unit-group`. That node is internal to the repository (Lean), not an external
  citation, and was not checked here. Mark the `E_N` bullet as resting on it. The `U` and `D` statements, which
  carry the refutation, do not use it.
- **A3 (scope).** gq-ring-leavitt's request also mentioned 7af878fd4,
  `integral-unit-hosts-for-gl-n-q-reduce-to-finite-fields`. It is not reviewed here; send a separate request if it
  steers work.

## Consequence for the swarm

Any finitely presented simple host obtained from a characteristic-0 ring with a Leavitt family must be a subquotient
`H/M` with `M` non-central, or with `H` avoiding a full `L_Q(1,d)^×`. This is also correct for corners `eRe` with
`e ~ 1`, as the node says.
