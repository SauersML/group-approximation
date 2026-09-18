# Referee report (gq-referee-a, proof-gap lens): reformulations of pgl-q-projective-type-a-extension

**Reviewed:** the hand-proved reformulations and Attempts 2–3 of `pgl-q-projective-type-a-extension`
(lane gq-typeA-projective), read on origin/main. The claim itself is OPEN.

**Verdict: PASS.** The reformulations and Attempts 2 and 3 are correct. One wording fix is needed.
Attempt 1 relies on `germ-extensions-omit-standard-gl-n-q`, which I have not reviewed.

## Strong form
- `PGL_m(Q)` acts faithfully and 2-transitively on `P^{m−1}(Q)`, so every `Γ` between it and
  `Sym(P^{m−1}(Q))` is faithful and transitive, with one orbit on 2-subsets.
- Point stabilizers are all conjugate. So type (A) reduces to two conditions: `Γ` finitely presented
  and one point stabilizer finitely generated.
- The finitary-alternating remark uses the reviewed stabilizer proof (09d5b4797). Correct.

## Subgroup form (equivalence)
- **Sufficiency.** Take `S = S_1 ⊔ Γ/Λ`. The `Γ`-orbits on 2-subsets fall into three kinds:
  - pairs within `S_1`: finitely many, by hypothesis;
  - pairs within `Γ/Λ`: they correspond to double cosets `ΛgΛ`, finitely many;
  - mixed pairs: they correspond to `Λ`-orbits on `S_1`, finitely many.
- **Stabilizers.** They are those of `S_1`, together with the conjugates of `Λ`. All are finitely
  generated.
- **The point `s_0 = Λ`.** Primitivity of a 2-transitive action makes `P(Q)` maximal, and
  `PGL_m(Q) ⊄ Λ`, so `Λ ∩ PGL_m(Q) = P(Q)`.
- **Necessity.** `Λ = Stab_Γ(s_0)`. Finitely many pair orbits on `Γs_0` give finitely many double
  cosets. Finitely many mixed pair orbits give finitely many `Λ`-orbits on `S_1`. Correct.
- **Wording fix.** "a type (A) action on a set `S_1` (which may be empty)" should read "an action on
  `S_1` with finitely generated point stabilizers and finitely many orbits on 2-subsets". Faithfulness
  is imposed only on `S_1 ⊔ Γ/Λ`, and an action on the empty set is not faithful unless `Γ = 1`.
- **What `Λ` must be.** It contains `Q^{m−1}`, so it is not residually finite (O1). For `m = 2`,
  `Λ ∩ PGL_2(Q) = Aff(Q)`. Correct.

## Attempt 2 (near actions)
- **`h_γ` is unique.** A cofinite subset of `P^{m−1}(Q)` contains a projective frame, and a frame
  determines a projective map.
- **`γ ↦ h_γ` is a homomorphism.** `γδ` agrees with `h_γ h_δ` off `F_δ ∪ h_δ^{-1}(F_γ)`, which is
  finite.
- **Conclusion.** The image of a finitely generated `Γ` lies in some `PGL_m(Z[1/N])`. That cannot
  contain `PGL_m(Q)`, whose unipotent `Q` has all denominators. Correct.

## Attempt 3
- **The germ lemma applies.** It uses the reviewed germ lemma (09d5b4797, fixed at 5d52aa4f1).
  - The germ group at an accumulating rational point is finitely generated.
  - By the identity principle, it contains `P(Q)` as a subgroup of germs, so it is not residually
    finite.
- **The reduction is correct:** it moves the problem one level down, to germs at a point.

## Summary for the coordinator
The strong form is now pinned down. It asks for a finitely presented `Γ ≤ Sym(P^{m−1}(Q))` that
contains `PGL_m(Q)` and has a finitely generated point stabilizer. The natural, near and piecewise
hosts are excluded. The remaining host must be non-locally-projective, and it must carry non-residually-
finite, finitely generated germ groups at rational points.
