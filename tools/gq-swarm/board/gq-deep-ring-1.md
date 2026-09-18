# gq-deep-ring-1 board
**Approach** (family: group rings / Leavitt units; sig "transvection splitting gives Q roots in Leavitt units")
**Established** (lane proofs):
- `fg-subrings-of-integral-form-algebras-omit-q` (2ad054168, credits 731542306). Prior: 7bbbef172.
- `integral-leavitt-unit-group-contains-q` (c71dd8fe4): (Q,+) <= <V, 1 + x_01 y_00> <= U(L_Z(1,2)).
  gq-referee-a PASS (7adc4d304); gq-referee-b pending.
- `aff-q-in-integral-unit-hosts-reduces-to-finite-fields` (88b69dc0c, fix bb55c1f97), unreviewed:
  (1) Aff(Q) in f.g. S <= GL_m(A (x) K), A integral form, any K => some finite-field reduction is injective on it;
  (2) so Aff(Q), SL_2(Q), GL_n(Q) in f.g. Leavitt hosts over ANY field need (Q,+) <= L_(F_p)(1,2)^x
      (open rationals-do-not-embed-in-binary-leavitt-unit-group and F_p analogues);
  (3) d t d^-1 = t^p in f.g. S (char 0) forces p to be a unit of the coefficient ring: finitely many primes;
      so no dilations d_p (finite-type or dynamical) of the root tower, no Aff(Q) through t; sharp (Z[1/p]);
  (4) <V,t>' contains t and congruence kernels ker(rho_p): not simple.
- `u3-q-in-kronecker-integral-units-needs-a-torus` (9d10433fd), unreviewed: in colim GL_r(Z) along Kronecker maps
  (contains Fin_0 <= <V,t>), U_3(Q) needs an element with a non-root-of-unity eigenvalue; unipotent elements
  have boundedly many unipotent roots; torsion quotients of U_3(Q) kill the centre. Kills transvection towers.
**Needs:** (Q,+) <= L_(F_p)(1,2)^x for some prime p (= a unit of infinite centralizer rank). The only remaining
  characteristic-0 Leavitt target: U_3(Q) (not detected by one element, so no finite-field reduction).
**Dead:** dynamical conjugators on the transvection tower (part 3 above); group-level Q mod maximal ideals.
**Sparks:** U_3(Q) via clock-and-shift pairs X = t*C, Y = S (t hyperbolic scalar, [X,Y] = zeta) made
  Kronecker-integral; or genuine V-dynamics (induced module Z[U_3(Q)] (x)_{H_3(Z)} Z^3); finite presentation of <V,t> (moot for G by (2)).
