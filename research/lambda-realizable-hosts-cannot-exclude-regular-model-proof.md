---
rg: 2
id: lambda-realizable-hosts-cannot-exclude-regular-model-proof
kind: route
title: Realize (ker lambda_H, tau_H) by a matrix model via TWW or unique trace, identify lambda_G restricted to H with an amplification of lambda_H, and run the representation-generic argument on lambda_Delta
target: lambda-realizable-hosts-cannot-exclude-regular-model
requires:
  - amenable-implies-operator-mf
  - native-cross-gram-conclusions-fail-in-every-tracial-model
artifacts:
  - non_mf_groups_exist.tex
---

Notation is that of the target.  `Q=prod M_(k_n)/sum M_(k_n)`.  `tr` is the
normalized trace.  For a free ultrafilter `omega`, `tau_omega` is
`lim_omega tr`, which is well defined on `Q` because `||x_n|| -> 0` forces
`tr x_n -> 0`.

## Step 0: from an embedding with the right trace to a model

**Lemma 0.** Let `A` be a unital separable C*-algebra with marked unitaries
`u_h`, `h in H`, and let `iota: A -> Q` be an injective *-homomorphism.
Suppose `p=iota(1)` satisfies `tau_omega(p)>0` for every `omega`.  Then there
is an MF model `W` of `H` such that:
- `rho_W = iota o q_A`, where `q_A: C*(H) -> A` sends `h` to `u_h`, after
  identifying `pQp` with `prod p_nM_(k_n)p_n / sum`;
- `tr_(rank p_n) W_n(h) -> tau_omega(iota(u_h))/tau_omega(p)` along `omega`.

*Proof.*
1. Lift `p` to self-adjoint `a_n` with `||a_n^2-a_n|| -> 0`.  Then
   `p_n = chi_[1/2,infinity)(a_n)` is a projection lifting `p`, and
   `pQp = prod p_nMp_n / sum p_nMp_n`.
2. Lift `iota(u_h)` to `x_n` in `p_nMp_n`.  Then `||x_n^*x_n-p_n|| -> 0` and
   `||x_nx_n^*-p_n|| -> 0`.  For large `n`, `x_n` is invertible in
   `p_nMp_n`.  Its polar part `W_n(h)` is unitary, and
   `||W_n(h)-x_n|| -> 0`.
3. Hence `||W_n(gh)-W_n(g)W_n(h)|| -> 0`, and `rho_W(h)=iota(u_h)`.
4. Traces change by `o(1)`, and the normalization by `rank p_n` divides by
   `tau_omega(p)`.  QED.

## Step 1: realizable hosts

**(b) `C*_r(H)` MF with unique trace.**
1. By the definition of MF, there is an injective `iota: C*_r(H) -> Q`.
   Then `p=iota(1) != 0`, so `||p_n|| = 1` eventually.
2. Apply Lemma 0 to the compression.  Take the model's normalized trace on
   `p_nMp_n`.
3. Work in the corner `prod p_nMp_n / sum`, with its own normalized traces
   `tr_(rank p_n)`.  For every `omega`, `x -> lim_omega tr_(rank p_n)` of a
   lift of `iota(x)` is a tracial state on `C*_r(H)`.  By uniqueness it
   equals `tau_H`.  (The hypothesis `tau_omega(p)>0` in Lemma 0 is needed
   only to compare with the uncompressed trace, and it is not used here.)
4. Hence `tr W_n(h) -> delta_(h,e)` along every `omega`, so along the
   sequence.
5. `ker rho_W = ker(q_A) = ker lambda_H` because `iota` is injective.

**Free groups.** Haagerup--Thorbjornsen (Ann. of Math. 162 (2005),
"A new application of random matrices: Ext(C*_red(F_2)) is not a group")
prove that `C*_r(F_2)` is MF, via GUE strong convergence.
- `C*_r(F_r) <= C*_r(F_2)` for `r <= infinity`, and a C*-subalgebra of an MF
  algebra is MF.
- `C*_r(F_r)` has a unique trace for `r >= 2` (Powers).

So (b) applies.

**(a) `H` amenable.**
1. `A=C*_r(H)` is separable and nuclear, satisfies the UCT (Tu), and
   `tau_H` is faithful.
2. Tikuisis--White--Winter (Ann. of Math. 185 (2017), Theorem A) make
   `tau_H` quasidiagonal.  This gives ccp maps `phi_n: A -> M_(m_n)` with:
   - `||phi_n(ab)-phi_n(a)phi_n(b)|| -> 0`;
   - `tr phi_n(a) -> tau_H(a)`.
3. Their Corollary C makes `A` quasidiagonal.  This gives ccp maps
   `psi_n: A -> M_(l_n)`, asymptotically multiplicative, with
   `||psi_n(a)|| -> ||a||`.
4. Put `Theta_n = phi_n^(direct sum r_n) direct_sum psi_n`, with `r_n` so
   large that `l_n/(r_nm_n+l_n) -> 0`.  Then:
   - `Theta_n` is asymptotically multiplicative;
   - `||Theta_n(a)|| = max(||phi_n(a)||, ||psi_n(a)||) -> ||a||`, since
     `limsup ||phi_n(a)|| <= ||a||`;
   - `tr Theta_n(a) -> tau_H(a)`.
5. So `iota=[Theta_n]` is an injective *-homomorphism with
   `tau_omega o iota = tau_H` and `tau_omega(iota(1))=1`.
6. Lemma 0 gives the model.  The corner normalization factor tends to `1`.

This is Schafhauser's Theorem 2.3 in his stronger convention, as recorded in
`amenable-implies-operator-mf-citation`.

## Step 2: blindness

1. Let `W` be the realizing model.  For every `omega`, the H-level datum of
   `(rho_W, tau_omega)` is `(ker lambda_H, tau_H)`.
2. `W` is an MF model with `tr W_n(h) -> 0` for `h != e`.  By hypothesis,
   `P` holds for this datum.
3. Decompose `G` into right cosets `Hg`.  The map `delta_(hg) -> delta_h`
   identifies `l^2(Hg)` `H`-equivariantly with `l^2(H)`.  So `lambda_G|_H`
   is unitarily equivalent to `lambda_H` tensored with the identity on
   `l^2(H\G)`.
4. An amplification has the same kernel on `C*(H)`.  Also
   `tau_G(lambda_G(h)) = delta_(h,e) = tau_H(h)`.
5. So the datum of `(lambda_G|_H, tau_G)` is `(ker lambda_H, tau_H)`, and
   `P` holds for it.  QED.

## Step 3: the kill

1. Let `Arg` be an argument of the stated form.  For every unital
   representation `rho` of `C*(Delta)` into a tracial C*-algebra `(B,tau)`,
   it proves:

   `Hyp(rho)` and `P_1(rho|_(H_1))`, ..., `P_m(rho|_(H_m))` imply `Lock(rho)`.

2. Take `rho = lambda_Delta` with `tau_Delta`.
   - `Hyp(lambda_Delta)` holds: exact rows, full carrier, and
     `tau((1-lambda(z))/2)=1/2`.  This is item 1 of
     `native-cross-gram-conclusions-fail-in-every-tracial-model`, as quoted
     in the target's reframing Attempt.
   - Each `P_i(lambda_Delta|_(H_i))` holds by Step 2.
3. So `Lock(lambda_Delta)`, which is `(XCG)` for `lambda`.  Item 1 of that
   node says this fails.  Hence `Arg` is invalid.
4. The obstruction is exactly the gauge-lock clause: every other hypothesis
   is satisfied by `lambda_Delta`.

**The pi_Q branch collapses to the lambda branch.**
- Every surviving norm-corona profile `sigma` is an MF model of `Delta`.
  So `sigma|_H` is an MF model of `H`, and `P` holds for it by hypothesis.
- So an H-level input that is true for all MF models of `H` excludes no
  profile by itself.  It can act only through a derivation, and a
  representation-generic derivation is refuted above.
- Therefore the input the target asks for, "false for `lambda` or for
  `pi_Q`", cannot be carried by a lambda-realizable host.  It needs a
  non-realizable host, or a derivation that is not valid in tracial
  C*-algebras, that is, one that uses matrix dimension beyond the
  `(ker, tau)` of every host.

## Scope and honesty notes

- This is a kill of a class of approaches.  It does not decide the target,
  which stays **OPEN** as recorded.
- The literature imports are TWW Theorem A and Corollary C, Tu's UCT for
  amenable groupoids, Haagerup--Thorbjornsen, and Powers.  They were not
  re-read in this session.  The amenable case is already bound in
  `amenable-implies-operator-mf-citation`.
