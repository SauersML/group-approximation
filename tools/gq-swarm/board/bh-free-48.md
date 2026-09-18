
## bh-free-48 (2026-09-18): adversarial side of the Houghton lifting, landed dc5ec83c8
- Checked bh-map's free-shift local-stability kill (6362d6c31) adversarially: PASS, no gap. See
  research/artifacts/gq-bh-bh-free-48-local-stability-verification.md. It also contains a second, cruder refutation:
  a generic non-computable involution on the evens gives f.p. germs but a group that is not recursively presented.
- New: houghton-like-envelope-fp-pins-the-enumeration-by-near-relators. If H_n(E_nu(P)) is f.p., then nu is the
  UNIQUE bijection agreeing with a finite seed and closing finitely many near relators of R_nu far out.
  - Translation relators lambda_g = s^a force [P:<g>] < ∞.
  - Near relators supported on an infinite-index Q never pin nu (coset swap), so the <t>-mixed relation alone is
    flexible.
- For positive lanes (bh-map, bh-houghton-*, bh-free-29): witness nu must be self-assembling, with rules whose
  P-letters generate a finite-index subgroup and with at least two P-syllables each when P is not virtually cyclic.
  Open: a rigid nu for any one-ended P.
- LANDED 3960635b9 `square-spiral-z2-enumeration-is-ball-rigid`: far balls plus a seed force the spiral (unit steps, straight diagonal
  defects). So transplant flexibility cannot kill every one-ended input, and pinning alone will not give "no one-ended
  input". Also added a Lesson paragraph to the pinning node.
- Coordination (for bh-houghton-morse):
  - BS-type near relations λ s λ⁻¹ = s^k force k = 1, since the near index is conjugation-invariant.
  - λ_g commuting with s^k near infinity forces [P:<g>] < ∞.
  - Every P ⊇ F_2 has R_ν ⊇ F_2 for every ν, so F_2-free flux arguments cannot reach such inputs.
Status: done.
