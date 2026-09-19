---
rg: 2
id: lambda-realizable-hosts-cannot-exclude-regular-model
kind: claim
title: A subgroup whose regular representation has a strongly convergent matrix model (every amenable or free subgroup) supplies only inputs that the regular representation of the ambient group satisfies, so no host-subgroup input on such a host can exclude lambda at the native cross-Gram gauge lock
distinct_from:
  amenable-subgroup-fixed-projection-is-never-in-adjoint-corona: that kills one Delta-level quantity (P_L in the adjoint corona) for amenable L in delta_e-profile models; this kills every H-level input, of any kind that depends only on the kernel and trace of the restricted representation, for every lambda-realizable H, amenable or not (free, surface, unique-trace MF).
  native-cross-gram-conclusions-fail-in-every-tracial-model: that shows the cross-Gram conclusion fails in every tracial model, so an input false for lambda is needed; this shows that no input read off a lambda-realizable host subgroup is ever false for lambda.
  haagerup-hosts-blind-full-group-kazhdan-certificate: that kills Theorem C certificates for Haagerup acting groups via finite orbits; this kills host inputs for the lambda-exclusion step via strongly convergent models of lambda_H.
  reduced-mf-kazhdan-subgroup-gate: that is descent of reduced MF to subgroups; this uses reduced MF plus trace control of a subgroup as the obstruction to that subgroup being a useful host.
artifacts:
  - research/lambda-realizable-hosts-cannot-exclude-regular-model-proof.md
---

**ESTABLISHED KILL (written proof; not Lean-verified).**

**Definitions.** Let `H` be a countable group.
- An *MF model* of `H` is a sequence of maps `W_n: H -> U(k_n)` with
  `||W_n(gh)-W_n(g)W_n(h)|| -> 0` in operator norm for all `g,h`.  It
  induces a unital *-homomorphism `rho_W: C*(H) -> Q:=prod M_(k_n)/sum M_(k_n)`.
  Each free ultrafilter `omega` gives a trace `tau_omega=lim_omega tr_(k_n)` on `Q`.
- An *H-level datum* of a unital representation `rho` of `C*(H)` into a
  C*-algebra with a trace `tau` is the pair `(ker rho, tau o rho)`.  An
  *H-level input* is a property `P` of such pairs.  Equivalently, `P` is a
  property of the tracial C*-algebra `(C*(H)/ker rho, tau)` with its marked
  group unitaries.  It covers the following:
  - every norm statement `||rho(x)|| <= c` or `>= c`, for `x` in `C H`;
  - spectral gaps, invertibility, and membership of a continuous functional
    calculus in `rho(C*H)`;
  - every trace value and every statement about the GNS von Neumann algebra
    of `tau o rho`.
- `H` is *lambda-realizable* if some MF model `W` of `H` has
  `ker rho_W = ker lambda_H` and `tr_(k_n) W_n(h) -> delta_(h,e)`.
  Equivalently, `||p(W_n)|| -> ||lambda_H(p)||` and `tr p(W_n) -> tau_H(p)`
  for every `p` in `C H`.

**Theorem.**
1. **Realizable hosts.** `H` is lambda-realizable in each of these cases:
   - (a) `H` is amenable;
   - (b) `C*_r(H)` is MF and has a unique tracial state, in particular for
     every nonabelian free group `F_r`, `r <= infinity`.
2. **Blindness.** Let `H <= G`, with `H` lambda-realizable, and let `P` be an
   H-level input that holds for every MF model of `H` (or for every MF model
   with `tr W_n(h) -> 0` for `h != e`, along every `omega`).  Then `P` holds
   for `(lambda_G|_H, tau_G)`.
3. **Kill at the gauge lock.** Take `G = Delta = St_20(L_(F_2)(1,2))`.  Consider
   any argument for `binary-leavitt-arbitrary-profile-native-cross-gram` of
   this form:
   - its hypotheses on the model are among those the target allows;
   - it adds an H-level input `P` on a lambda-realizable `H <= Delta` that is
     true for all MF models of `H`;
   - it is valid for every unital representation of `Delta` into a tracial
     C*-algebra satisfying those hypotheses and `P`, which is the
     representation-generic form of the reframing Attempt.

   Every such argument proves a false statement.  It dies at the gauge-lock
   clause: applied to `lambda_Delta`, it yields a lock that
   `native-cross-gram-conclusions-fail-in-every-tracial-model` refutes, with
   `epsilon_g >= 2/3`.  This holds for any finite family of such hosts and
   inputs at once.

**Invariant.** The pair `(ker, trace)` of `lambda_H`, together with
whether some matrix model of `H` realizes it.

**Survivors.** A host-geometry input can be false for `lambda` only in one of
two ways:
- (i) it is carried by a subgroup `H` that is **not** lambda-realizable, for
  example one with `C*_r(H)` not MF; or
- (ii) it is a genuinely Delta-level operator-norm statement, not a
  restriction to one subgroup.

Kazhdan hosts are excluded by the goal.  Every amenable subgroup of
`EL_n(J)` and every free subgroup of `Delta` is realizable, so it is dead.
A candidate for (i) is an `EL_N` subgroup over a measure-free Steinberg
algebra, whose `C*_r` is non-MF by
`measure-free-steinberg-el-n-reduced-cstar-not-mf`.  Whether that route uses
property (T) is not checked here.

Proof route: `lambda-realizable-hosts-cannot-exclude-regular-model-proof`.
