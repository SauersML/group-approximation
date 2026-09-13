# Class four at a finite stage, and why spin trapping cannot carry it

Date: 12 September 2026, lane `ex-unitary-class-three`. The argument is
complete but has not been independently reviewed. It continues
`class-three-spin-bordism-trapping-2026-09-12.md` (Part 1) and
`component-group-class-bound-by-excess-2026-09-12.md` (the excess bound).

## 1. C(T^3 x S^3, M_2) has class exactly four

Let alpha: S^1 -> U(2) be z -> diag(z, 1) and omega: S^3 = SU(2) ⊂ U(2). On
T^3 x S^3, with coordinates (s_1, s_2, s_3, z), put u_i = alpha o s_i and
v = omega o z, and set

    c_4 = [u_3, [u_2, [u_1, v]]].

**Proposition 1.1.** c_4 is not in U_0(C(T^3 x S^3, M_2)). Hence the
component group of C(T^3 x S^3, M_2) has class exactly four.

*Proof.* The lower bound comes in three steps.

*The class.* As in `u2-triple-samelson-eta-squared-proof`, naturality of
the Samelson product gives <alpha, omega o h> = <alpha, omega> o (1 ∧ h). With
<alpha, omega> = omega o eta_3, induction gives

    <alpha, <alpha, <alpha, omega>>> = omega o eta_3 o eta_4 o eta_5.

By Toda (Composition Methods, the 2-primary pi_6(S^3)), eta_3^3 = 6 nu' ≠ 0 in
pi_6(S^3) ≅ Z/12. Stably this is eta^3 = 12 nu ≠ 0 in pi_3^s ≅ Z/24, and it
is compatible with suspension. Toda's theorem number was not re-verified in
this lane.

*Factorization.* The commutator is 1 on the fat wedge, so c_4 factors as
cbar_4 o q with q: T^3 x S^3 -> S^6 and [cbar_4] = omega o eta_3^3.

*Detection.* Write T^3 x S^3 = S^1 x Y with Y = T^2 x S^3. The map vanishes on
{1} x Y, and that pair has a retraction. So
[Sigma(Y_+), U(2)] -> [S^1 x Y, U(2)] is injective, as in Proposition E of
`stw59-samelson-orders-and-wedged-arms-2026-09-11.md`. Then
Sigma(Y_+) ≃ S^1 ∨ Sigma Y. The suspension splitting of the product
T^2 x S^3 has the summand Sigma(S^1 ∧ S^1 ∧ S^3) = S^6, and the collapse onto
it has a homotopy section. So pi_6 U(2) -> [T^3 x S^3, U(2)] is injective,
and c_4 is not null-homotopic.

The upper bound: d = 6 and r = 2, so the excess is two, and the excess bound
gives class at most four. □

Nesting once more gives eta_3^4 = 6 nu' o eta_6. This is zero, because
nu' o eta_6 has order two in pi_7(S^3) ≅ Z/2. So this family of seeds stops
at class four.

## 2. Spin trapping is blind to eta cubed

Take the setting of Part 1, Proposition 2.1 with M = T^3 x S^3. Put
w = (c_4 o pr_M) (+) 1_Q. The trapped class is

    nu^M(w) = <c_r(Q)^2, [X]>·[T^3 x S^3, c_4]_red.

A regular preimage of c_4 is a framed 3-manifold in the open top cell. It
represents eta^3 = 12 nu in pi_3^s, and its spin bordism class lies in
Omega^Spin_3 = 0. So nu^M(w) = 0 for every X and Q. The detector is silent.
Silence does not show that w lies in U_0.

More generally, suppose the protected block C^2 carries a spin-trapped seed
that factors through a sphere collapse S^m -> SU(2). Its trapped class is the
image of a stable stem x in pi_{m-3}^s under the unit S -> MSpin, times an
Euler number. The unit is zero on eta^3, and on every element whose
KO-Hurewicz image vanishes in degrees 3 to 7. With rank-two protected blocks,
the reachable depth is therefore capped: nested alpha-brackets reach eta^2,
and eta^3 is invisible.

## 3. Routes toward a simple algebra of class four

- *String trapping.* MString_3 ≅ tmf_3 ≅ Z/24 sees nu, so it sees
  eta^3 = 12 nu. One needs closed string manifolds X^{4r} with complex Q of
  rank r such that W_R = (Q* (+) Q*)_R is string, that is
  p_1(Q_R) = c_1(Q)^2 − 2 c_2(Q) = 0. One also needs <c_r(Q)^2, [X]> odd and a
  recursion preserving all of this. Parity is
  <c_r(Q)^2, [X]> ≡ <v_{2r}(X) c_r(Q), [X]> mod 2, by the Wu formula. For
  string X, v_4 = 0 kills r = 2. The Cayley plane OP^2 has v_8 ≠ 0, but c_4
  of a complex bundle on its 8-cell is divisible by 3! = 6, so it fails at
  r = 4. No example is known to this lane.
- *Framed trapping.* The locus is stably framed when TX ≅_s W_R. Then W is a
  quaternionic bundle Q* (x)_C H, and the Euler number is χ(X) mod 2. The
  obvious candidates fail on p_1: Gr_2(C^4) has p_1 = 2h^2 against
  2(σ_2 − σ_11), and HP^2 would need c_2(Q) = −u/2.
- *Larger protected blocks.* Take C^k with W = k·Q*, and seeds in pi_*U(k) for
  k >= 3. Their spin-bordism images can use cells of SU(k) above the bottom
  one. The depth is not known to be capped there.
