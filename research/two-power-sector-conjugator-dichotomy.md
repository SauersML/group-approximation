---
rg: 2
id: two-power-sector-conjugator-dichotomy
kind: claim
title: Property T makes the two-power corrector all-or-nothing, and the sector is a Jung-type embedding question
distinct_from:
  two-adic-tower-format-of-surviving-lambda-exact-enemy: that assembles the data format the surviving enemy must carry; this proves its corrector subproblem has NO asymptotic middle ground -- an exact conjugator exists in the ultraproduct, or every candidate is uniformly obstructed at a Kazhdan floor -- and identifies which question decides between them.
  odd-congruence-lambda-exact-sector-collapses: that closes the odd sector by evaluating the corrector to 1 against the exact slot; this treats the 2-power sector, where no slot exists, and replaces evaluation by an embedding-rigidity dichotomy plus a torsor cohomology reformulation of what remains.
  one-commutator-controls-distance-to-full-commutant: that is a Poincare modulus for Lambda-central vectors against the full commutant; this is rigidity at the level of EMBEDDINGS of the parahoric group algebra, with the conjugator itself as the almost-central bimodule vector.
---

Let `A = (e_21(2), e_31(4), e_32(2), e_12(1), e_13(1), e_23(1))` and
`B = h A h^(-1) = (e_21(1), e_31(1), e_32(1), e_12(2), e_13(4),
e_23(2))`, two 6-tuples in `Lambda = SL_3(Z)`, and let
`Lambda_0 = <A>` (which contains a relative elementary congruence
subgroup, hence has finite index in `SL_3(Z)`, hence property (T)
with a Kazhdan pair `(A, epsilon_0)`).  Fix any 2-power congruence
tower of genuine representations `sigma_m` of `Lambda` (regular type
or not) and the tracial ultraproduct `M` of the corresponding matrix
algebras.  Then:

1. **Moment equality.**  For every word `w`, `w(B) = h w(A) h^(-1)`
   exactly over `Z[1/2]`, so for every fixed `w` and all
   sufficiently deep levels, `w(A) = 1 mod 2^a` iff
   `w(B) = 1 mod 2^a`: in `M` the tuples `pi(A)`, `pi(B)` have equal
   mixed `*`-moments, and both generate a copy of the non-amenable
   group von Neumann limit of `Lambda_0` -- so Jung's uniqueness
   theorem for embeddings (amenable case) does NOT apply, and
   conjugacy of the two embeddings is a genuine question.

2. **Dichotomy.**  Either there is a unitary `V in M` with
   `V pi(A_i) V^* = pi(B_i)` EXACTLY for all `i`, or EVERY unitary
   `V in M` satisfies

   ```text
   max_i || V pi(A_i) V^* - pi(B_i) ||_2  >=  delta_0 > 0,   (CD1)
   ```

   with `delta_0` depending only on the Kazhdan constant of
   `Lambda_0`.  There is no asymptotic middle regime: an enemy of
   the 2-power `Lambda`-exact sector requires the FIRST branch,
   since its corrector satisfies the six intertwinings exactly in
   the ultraproduct.

3. **What remains on the conjugacy branch.**  If a conjugator
   `V_infty` exists, the set of all of them is the torsor
   `V_infty U(C)`, `C = pi(B-side)(Lambda_0)' cap M`, and the
   remaining enemy constraints -- the Weyl inversion, the three-term
   interlock, commutation of the Weyl orbit, the Haar tower and
   mixed-trace regularity -- become equations ON THE TORSOR: their
   solvability is a cocycle condition for the Weyl action twisted by
   `V_infty` with coefficients in `U(C)`.  So the whole 2-power
   sector reduces to (i) one yes/no embedding-conjugacy question for
   an explicit moment-equal pair, and (ii) on a YES, one
   Weyl-cohomological selection problem on an explicit torsor.

## Attempts

- **Which branch to expect.**  A NO closes the 2-power
  `Lambda`-exact sector outright (with the odd sector already
  closed by `odd-congruence-lambda-exact-sector-collapses`, all
  `Lambda`-exact microstates would then be dead and the enemy fully
  confined to uniform outliers).  Known technology for proving
  non-conjugacy of specific moment-equal embeddings of property (T)
  algebras: N. Brown's convex structure on `Hom(N, R^omega)` modulo
  conjugacy, and its (T)-discreteness (embeddings of (T) algebras
  are isolated points -- consistent with, and the deeper reason
  behind, the dichotomy above); Hayes-type entropy invariants vanish
  here (both sides strongly 1-bounded), so a distinguishing
  invariant must be finer -- e.g. the relative position of the two
  copies inside the group-algebra ultraproduct, where the conjugator
  is forced to be "quantum": no group element of any finite level
  conjugates (`g` would have to agree with `h` up to centralizers,
  and `h` is not integral), so a YES needs a genuinely
  non-group-like unitary against two (T)-rigid subalgebras.
- **The conjugacy branch is a model question for an arithmetic
  mapping torus — and finite quotients can never witness it
  (2026-08-21, follow-up).**  An exact conjugator `V` together with
  `pi|_Lambda` is precisely a unitary representation of the partial
  HNN extension `G_0 = HNN(SL_3(Z), Lambda_-, Lambda_+, Ad h)` (not
  ascending: both associated subgroups are proper, so the
  established `ascending-hnn-cannot-create-nonhyperlinearity`
  permanence does not apply) whose `Lambda`-restriction is 2-power
  congruence exact.  KERNEL-INVARIANCE NO-GO: a finite quotient
  `q : G_0 -> F` needs `q(v)`-conjugation to implement `Ad(h)` on
  the image, which forces `h (ker q cap Lambda_-) h^(-1) subseteq
  ker q`; a 2-power principal congruence kernel violates this (the
  sharp depth-two corner shift of
  `two-adic-tower-format-of-surviving-lambda-exact-enemy` maps
  `Lambda(2^a) cap Lambda_-` outside `Lambda(2^a)`), while ODD
  congruence kernels satisfy it exactly (`Ad(h)` is an isomorphism
  mod odd `n`) — and the odd-exact world is already closed by
  `odd-congruence-lambda-exact-sector-collapses`.  Consequently no
  conjugator lifts from finite quotients of `G_0`: if the conjugacy
  branch holds at all, its witness is a genuinely quantum unitary
  invisible to every finite quotient — the same
  non-residually-witnessable character as the uniform-outlier
  residue, now appearing at the embedding level.
- **The probe connection.**  `(CD1)` predicts the tower probes on
  regular-type modules see either defect `-> 0` (conjugacy branch)
  or a floor `>= delta_0` -- never a slow drift to zero; the
  measured `s = 1` floor `32/21` is consistent with either branch
  (bounded-multiplicity modules are obstructed for the independent
  Hoffman--Wielandt reason).  A measured floor BELOW any certified
  `delta_0` at deep regular levels would certify the conjugacy
  branch and redirect all effort to the torsor selection problem.
- **Falsification honesty.**  A YES on conjugacy does not produce an
  enemy: the torsor selection carries the Weyl/trace constraints
  that killed the odd sector, and the `SL_2`-fork lesson applies --
  a fully solvable selection would instead be evidence toward
  hyperlinearity of the carrier, making this dichotomy a genuine
  two-sided instrument.
