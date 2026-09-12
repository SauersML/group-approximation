# kh-ejz lane report (2026-09-11/12)

Scope: property (T) of GHB(7) for kh-hyperbolic's insurance route (CCKW GHB(7) → LatticeRouteInput),
the `hT` leaf of kh-cckw's `ghb7LatticeRouteInput`: `KMSGroup.GHBQuotient.hasKazhdanPropertyT_ghb7`.

## Model test (acn112, seconds): $NM/backup/kh-ejz/kms_angle_model_test.py
- Regular-representation angles of the CCKW Prop 7.15 images in SL4(F7): <a,b> (343) 0.377964 = 1/√7;
  <c,b>, <c,a> (2401) 0.534522 = √(2/7).
- 1/√2 (HeisenbergAngleBound) FAILS both EJZ Cor 3.3 and Thm 5.9 for GHB(7).
- Sharp angles pass Cor 3.3: eps0 = 0.958 < 1.  Rational constants: e3 = 0.378, e1 = e2 = 0.5346,
  eps0 = 0.96.
- U4 key inequality Σ_{0<m<p} ⟨x, b^m x⟩ / ‖x‖² ≤ 0.22 on samples (claim ≤ 1).

## GREEN, landed
- PropertyT/ThreeVertexDuality: EJZ Lemma 2.4 (density form), Lemma 2.5.
- PropertyT/ThreeVertexClosure: closures, EJZ (3.3), two-subspace estimate.
- PropertyT/ThreeVertexProposition: EJZ Prop 3.2 in Hilbert form (density replaces X + Y = U).
- PropertyT/ThreeVertexKazhdan: MovingAngleLE, isKazhdanSubset_of_movingAngles (EJZ Cor 3.3(a)).
- Kazhdan/EJZAngleTranslates: translate sums; twisted fixed vectors orthogonal off V^z.
- Kazhdan/EJZAngleHeisenberg: movingAngleLE_heisenberg (1/√p, CCKW Prop 7.3(i), character-free).
- Kazhdan/EJZAngleBessel: Bessel for translate sums over transversal cyclic subgroups; w^i z^j calculus.
- Kazhdan/EJZAngleSylowFourGram: a b^m = b^m a w^m z^{m(m-1)/2}; Gram-sum bound for U4(p).

## AUTHORED, landed unverified, probe running
- Kazhdan/EJZAngleSylowFour: movingAngleLE_sylowFour (√(2/p), CCKW Prop 7.3(ii), character-free).
- Kazhdan/EJZAngleGHB: hasKazhdanPropertyT_ghb7.

## TRAPS
- `omit [..] in` must precede the docstring, not sit between docstring and theorem.
- `Finset.add_sum_erase _ _ h` cannot infer the summand: pass the lambda explicitly.
- `gcongr` may discharge side goals itself; following `·` bullets then fail with "no goals".
- Unused simp args are errors (`simp [real_inner_self_eq_norm_sq]` when simp closes without it).
