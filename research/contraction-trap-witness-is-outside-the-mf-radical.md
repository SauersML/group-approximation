---
rg: 2
id: contraction-trap-witness-is-outside-the-mf-radical
kind: claim
title: The rank-three contraction-trap witness w = [e, g^-1 a1 g] of EL_3(J) survives in an amenable quotient of Gamma_3, so w is not in Rad_MF(Gamma_3); more generally every universal contraction trap on a free base that passes the metabelian Fox test has its witness outside the MF radical, so contraction traps prove non-LEF but never put anything into an MF radical
distinct_from:
  contraction-trap-groups-are-sofic: that proves the universal trap groups sofic (tracial and Hamming approximations) and explicitly does not claim MF; this is the operator-norm statement, for which soficity gives nothing, and it is proved by an explicit solvable quotient found by Fox calculus, not by the Stallings separability telescope.
  alpha-amenably-separable-base-keeps-compression-witness-mf: that is the compression wreath K^(V/Gamma) x| V with the lamp criterion (B) and the squaring example on F_2, where a nilpotent (Magnus power-series) quotient separates; for the rank-three trap every nilpotent and every abelian quotient fails (phi_C is bijective on F_ab and on F/gamma_n), and so does every quotient on which g fixes the characters of F; the separating quotient here is metabelian-by-cyclic and needs g to move characters.
  jacobson-el3-is-not-lef: that proves every finite quotient of Gamma_3 kills w; this shows an amenable (solvable-by-lamp) quotient of Gamma_3 does not, so the finite-quotient collapse has no operator-norm analogue from the trap relations alone.
  jacobson-coherent-group-is-not-mf-via-kazhdan-transport: that puts x_13(Q) into Rad_MF of an ascending HNN group through property (T) of EL_3(J); this shows the Kazhdan input is indispensable there in the sense that the bare trap presentation, which is (T)-free, keeps its witness outside Rad_MF.
artifacts:
  - experiments/contraction-trap-mf-2026-09-17/fox_separation.py
  - experiments/contraction-trap-mf-2026-09-17/output.txt
---

**ESTABLISHED** (route `contraction-trap-witness-is-outside-the-mf-radical-proof`; swarm-0917 w15,
agent-verified, no referee). `fox_separation.py` exits 0 (20 exact checks over `Z[A]` and `F_p`;
transcript in `output.txt`).
No property (T), no trace and no soficity is used.

**Setting.** `F` is free on `x_1..x_n`, `phi : F -> F` an endomorphism, and
`T(F, phi) = < F, g, e | g x g^-1 = phi(x), [e, x] = 1 (x in F) >` is the universal contraction-trap
group, with witness `w_x = [e, g^-1 x g]` for a basis letter `x`. Put `A = F_ab = Z^n`, written
multiplicatively with basis `x_1..x_n`, and `G = Z[A]^n x| A`, the Magnus group, with product
`(a, f)(b, h) = (ab, f + a h)` on row vectors. The Magnus map `mg : F -> G` is `x_i -> (x_i, e_i)`.
The **abelianized Fox Jacobian** is the `n x n` matrix over `Z[A]` with rows
`D_j = ((d phi(x_j) / d x_i)^ab)_i`, so that `mg(phi(x_j)) = (phi_ab(x_j), D_j)`.

**Metabelian Fox test.** `(F, phi, x)` *passes* if
1. **(FT-1)** `phi_ab` is injective on `A` and `det D != 0` in `Q(A)`, and
2. **(FT-2)** `e_x` is not of the form `h D` with `h in Z[A]^n`.

Condition (FT-2) holds as soon as some point `z in (k^x)^n` over a field `k` has `e_x` outside the row space
of `D(z)`.

**Theorem.**
1. **(FT1) Separation.** If `(F, phi, x)` passes, then `w_x` is not in `Rad_MF(T(F, phi))`. More
   precisely, `T(F, phi)` maps to the amenable group `(Z/2)^(Q/P) x| Q`, with `w_x` nontrivial there.
   Here `Q` is the ascending HNN extension of `G` along `Phi(a, f) = (phi_ab(a), phi_ab(f) D)`, which is
   solvable of derived length at most 3, and `P = mg(F)`.
2. **(FT2) The rank-three trap passes.** Take `Gamma_3 = T(F_6, phi_C)`, the certificate group of
   `jacobson-el3-is-not-lef`, with `x = a1`. Then:
   * `phi_ab` lies in `GL_6(Z)`;
   * `det D = -x2^6 x3^2 P_C / (x1^6 x4^4 x6)`, where
     `P_C = x1x3x4x5x6 - x1x3x4x5 + x1x4x5x6 - x1x4x6 - x2^2x3x5x6 + x3x4x5x6 - x3x4x6`
     is not a unit of `Z[A]`;
   * at `z = (4, 4, 2, 1, 4, 1)` over `F_5` one has `P_C(z) = 0`, `rank D(z) = 5`, and `e_1` is not in
     the row space.

   Hence `w = [e, g^-1 a1 g]` is not in `Rad_MF(Gamma_3)`. This is the element that maps to `x_23(-sq)` in
   `EL_3(R)`.
3. **(FT3) Why simpler quotients fail.**
   * **Nilpotent images fail.** Every quotient of `Gamma_3` in which the image of `F_6` is nilpotent
     kills `w`. The reason is that `phi_ab` is onto, so `phi(F) F' = F`, and in a nilpotent group a
     subgroup onto the abelianization is everything.
   * **Rank-one affine images fail.** Every homomorphism `M = <F_6, g | C1-C6> -> Aff(K)`, for any
     field `K`, kills `w`.
     * The linear parts commute, so the character is `phi`-fixed: `a1, a2 -> alpha`, `a3, a4 -> beta`,
       `c, d -> 1`.
     * On that torus `det(D - gamma) = (alpha^2 + beta gamma)(gamma - 1)^4 (gamma + 1) / beta`, so
       `det D = alpha^2 / beta` is a unit.
     * If `g -> (gamma, nu)` with `gamma != 1`, conjugate to `nu = 0`. Then (C1) gives
       `mu_{a2} = gamma mu_{a1}`, so `(gamma^-1 - 1) mu_{a1} = gamma^-1 mu_{a1 a2^-1}`.
     * The eigenvalue `gamma` is `-1` or `-alpha^2/beta`, a unit of `Z[alpha^+-1, beta^+-1]`. So this
       element lies in the translation module of the image of `F_6`, and `g^-1 a1 g` lands in that image.
     * If `gamma = 1`, then (C1) gives `(alpha - 1) nu = mu_{a1 a2^-1}`, and the same conclusion holds.
   * **So a separating amenable quotient of `Gamma_3` must let `g` move the characters of `F_6`.** The
     Magnus quotient `Q` does this, since `t` acts on `A` by `phi_ab`. The obstruction polynomial `P_C`
     restricts to the unit `-alpha^2 beta` on the `phi`-fixed torus.
4. **(FT4) Calibration.**
   * The Baumslag-Solitar toy trap `a -> a^2` passes, with `D = 1 + x` and `e_1` outside the row space
     at `x = -1`.
   * The automorphism `a1 -> a1 a2`, `a2 -> a2` fails, as it must, since `D` is invertible over `Z[A]`.

## Class kill (operator-norm contraction traps)

* **Class.** Arguments that derive "`sigma(w_x) -> 1` in operator norm for every asymptotic unitary
  representation of `G`", that is `w_x in Rad_MF(G)`, from a contraction-trap certificate
  `T(F, phi) -> G` on a free base alone. By `mf-radical-functoriality` this is the same as proving
  `w_x in Rad_MF(T(F, phi))`. Members:
  * the rank-three trap of `EL_3(J)`, `EL_3(R)` (`ts = 1 != st`) and `EL_3(Z<S,T|TS=1>)`;
  * every trap that passes the Fox test, including all Baumslag-Solitar traps `a -> a^m` with `|m| >= 2`;
  * every "co-Hopfian hull, so `Ad sigma(g)` is onto" argument transplanted from finite models to
    operator-norm models.
* **Invariant.** The injective endomorphism `Phi` of the Magnus group `G`, through the abelianized Fox
  Jacobian `D`. Equivalently: whether `e_x` lies in `Z[A]^n D`.
* **Step where every member dies.** "Injective endomorphism of the hull, hence onto." The MF model `H`
  built from `Q` refutes it. In `H`, `Ad t` maps the hull `G` of `P` injectively into itself but not
  onto, because `det D` has the non-unit factor `P_C`. In that model `sigma(w)` is a lamp difference of
  norm distance `sqrt 2` from the identity in `C*_r(H)`, and `H` is MF (Tikuisis-White-Winter).
* **Consequence.**
  * Any proof that `x_23(sq)` lies in `Rad_MF(EL_3(J))` must use relations of `EL_3(J)` outside the
    12-relator certificate. The same holds for the (T)-free routes to `property-t-free-leavitt-full-mf-radical`
    that go through the Jacobson head (`property-t-free-jacobson-head-collapse`).
  * Examples of such relations are relations inside `A`, for instance that all six generators of `A` are
    involutions over `F_2`, or property (T).
  * Together with `contraction-trap-groups-are-sofic`, the bare trap certifies non-LEF and nothing
    else: it gives no MF, sofic or hyperlinear obstruction.

## What is not claimed

* That `Gamma_3` is MF (`Rad_MF(Gamma_3) = 1`). The kernel of `Gamma_3 -> M` is a free product of copies
  of `Z` indexed by `M/F_6`, not the abelian lamp group, so residual amenability of `Gamma_3` needs more
  than `Q`.
* Anything about the **enlarged** trap whose base is the true image of `A` in `EL_3(J)`.
  * Over `F_2` the six generators are involutions, and `c` commutes with `U a1 U^-1`.
  * The Magnus group over `Z[A]` does not respect these relations. Every metabelian quotient of an
    involution-generated base is virtually abelian.
  * This is the precise open extension. Call it **(E1)**: does some amenable quotient of
    `<A_J, g | g a g^-1 = Psi(a)>` separate `g^-1 a1 g` from `A_J`?
* A converse. Failing the Fox test only says that the metabelian Magnus quotient does not separate. By
  the Magnus image criterion it is equivalent to `x in phi(F) F''`. Other amenable quotients may still
  separate.

DERIVATION
contraction-trap-witness-is-outside-the-mf-radical-proof
