# Referee report (gq-referee-a, proof-gap lens): gq-pp-fp's divisible-circle proof

**Reviewed.** `research/artifacts/gq-gq-pp-fp-divisible-circle-proof.md` (lane gq-pp-fp), landed at
942cdfa94.

**Verdict: PASS.** Lemma A, Lemma B, §5 (items 1–5) and Corollaries 1–3 are correct. Four
non-blocking defects are listed in §4, and each has a one-line repair. Citations were not
re-checked.

**Relation to the landed claim.** The artifact says `pp-circle-divisible-subgroups-act-freely` "is
not on main yet". That is stale. The claim landed at d65ff92ff, with gq-pp-psl2q's own proof,
before this artifact landed, and it passed proof-gap review at 1c4d03cb4. The two proofs are
independent:
- psl2q argues through the gaps of one element and the germ at a gap endpoint;
- this artifact argues through Lemma A (no global fixed point for a copy of `Q`) and Lemma B
  (injectivity of `rot`).

Corollary 3 (finitely generated, finitely-pieced interval and line groups have no nontrivial
divisible subgroup) and the lift argument for `U_3(Q)` in Corollary 2 go beyond the landed nodes.

## 1. Lemma A (a copy of `(Q,+)` has no global fixed point)

- **Nested fixed sets.** Correct. Each `r_k` is a power of `r_{k+1}`, and
  `Fix(Q_0) = ∩_k Fix(r_k)`, which is nonempty by compactness when `rot ≡ 0`.
- **Step 1 (F3).** Correct. `Q_0` fixes `a`. Its right-germ image in `Stab_Λ(a)` is divisible
  abelian, so it is trivial by (D).
- **Step 3 (the point I was asked to attack).** Correct.
  - `C`, the component of `Fix(r_k)` that contains `a`, is a proper closed arc whose right end is
    `c_k`.
  - `r_{k+1}` commutes with `r_k` and fixes `a`, so it maps `C` onto `C`. Since it preserves
    orientation, it is increasing on `C`.
  - `(r_{k+1}|_C)^{k+1} = r_k|_C = id`, and an increasing periodic self-map of an interval is the
    identity. So `c_{k+1} ≥ c_k`.
  - This step is what stops the `c_k` from shrinking to `a`. It uses only commutation and
    orientation; the pieces play no role.
- **Step 4.** Correct. `Q_0 = ∪ <r_k>` is the identity on `(a, c_1)`, which meets `J`.

## 2. Lemma B (`rot` is injective on a copy of `Q`)

- **Step 1.** Correct. `K` is locally cyclic and countable, so it is an ascending union of cyclic
  groups, and the nested-compact argument gives `Fix(K) ≠ ∅`.
- **Step 2.** Correct. `Q_0` permutes the components of the complement of `Fix(K)`. A finite orbit
  would give a finite-index stabilizer, which is all of `Q`. That stabilizer fixes the endpoints of
  `J`, contradicting Lemma A.
- **Step 3.** Correct. `k = d k d^{-1}` is nontrivial on each `d(J)` and fixes its endpoints.
  - The orbit is infinite, so `Fix(K)` has infinitely many complementary components, each with two
    distinct endpoints.
- **Step 4.** Correct.
  - A point of `B_k` lies in the closures of at most two of the disjoint arcs, so all but finitely
    many arc-closures avoid `B_k`.
  - Each such closure lies in one component `I` of `S^1 \ B_k`.
  - (L): F2 kills one arc outright.
  - (P): two such arcs inside one proper `I` give at least three distinct fixed points of one
    nontrivial Möbius piece.
  - If `B_k = ∅`, the element is a single piece: a rotation in (L), or a Möbius map in (P) with at
    most two complementary arcs.

## 3. Sections 5–7

- **§5.** Correct. The chain `v_{k+1}^{k+1} = v_k` gives an injective `Q → D`. This uses only
  torsion-freeness of `<v>`, so it also works for nonabelian divisible `D`, as §7 needs.
  - Items 1–5 follow from Lemma B.
- **Corollary 1.** Correct.
  - Divisible or perfect subgroups lie in `Γ^+`. The acting elements lie in `Γ^+`: `t^2`, `x ↦ 4x`,
    `diag(2, 1/2)`, and `y(1)` in the divisible group `U_3(Q)`.
  - Orientation-preserving pieces of a `PGL_2(R)`-piecewise map lie in `PSL_2(R)`, since the sign of
    the derivative is the sign of `det`.
- **Corollary 2.** Correct, except for the omission in §4.3.
  - For `U_3(Q)`: `X ∩ Z = 1`, so `X̄ ≅ Q`. Then `rot(z̄(a)) = 0` by conjugation invariance inside
    the abelian group `X̄Z̄`.
  - `Z̄ = Z/C` is torsion when `C ≠ 1` is cyclic, so F1 forces `Z = C`. That is impossible.
- **Corollary 3.** Correct.
  - `∞` is a common fixed point in the projective case. Increasing Möbius pieces have `det > 0`, so
    they lie in `PSL_2(R)`, and the extension to `RP^1` adds one breakpoint at `∞`.
  - In the affine case, F3 at `±∞` holds for germs `x ↦ λx + c`.
  - Lemma A then runs as stated.

## 4. Non-blocking defects

1. **Lemma A, Step 1, "`c_k ∈ J̄`".** Unjustified: for small `k`, `r_k` may fix all of `J̄` and
   more. It is never used. Delete it.
2. **F2 (L), "the same `m` for both, by continuity along `Ĩ`".** Continuity alone does not give this.
   The right reason: for a lift `k̃` of an orientation-preserving circle homeomorphism, `k̃(x) − x`
   has oscillation `< 1` on each interval of length `< 1`, so two integer values coincide.
3. **Corollary 2 omits `Q ⋊_{−1} Z`.** Corollary 1 lists it (λ ≠ 1 when `Γ ≤ Homeo_+`), and
   `Γ̂ ≤ Homeo_+(R)`. Its centre `<t^2>` is infinite cyclic, so the "trivial or finite centre" bullet
   does not apply.
   - Uniform repair for every `λ ≠ 1`: `Q ∩ Z(H) = 0`, so `Q` embeds in the image, and the image of
     `t` acts on it by `λ ≠ 1`. Item 3 then gives a contradiction.
4. **§7, "the central `Q` of `T̄`".** Wrong. The centre of `T̄` is `<x ↦ x + 1> ≅ Z`. A central `Q`
   would map to the centre of the simple group `T`, so it would lie in `Z`. Say "the copy of `Q`".

## 5. Scope

- **Verdict §8 (one-dimensional finitely-pieced hosts are dead for `G` and the stepping stones).**
  Correct under the stated hypotheses: finitely many breakpoints per element, and pieces in a group
  satisfying (D).
- **Escapes E1–E3 correctly identified.** E1, singular points where F3 fails, is the live one. It is
  where `Q ≤ T̄ ≤ A ≤ VA` sits.
