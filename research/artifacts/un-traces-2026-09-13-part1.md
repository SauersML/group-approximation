---
rg: 2
title: "The trace face of the non-MF / Pestov 9.1 unification: QD collapses to residual finiteness, corona traces separate paradox from measure (2026-09-13)"
kind: artifact
---

Lane `un-traces` (UN swarm), 2026-09-13. Everything below is unreviewed except the verbatim imports.
Credits: Kirchberg (Math. Ann. 299 (1994) 551–563), Ozawa (arXiv:math/0306067v2), Ershov–Jaikin-Zapirain,
the non-MF manuscript (`non_mf_groups_exist.tex`, Thm l.1349 and Lemma `prop:mf-residual-calculus`), the
Pestov 9.1 artifact (`simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md` §3), lane `un-paradox`
(`stably-infinite-ring-elementary-groups-have-no-mf-quotient`), and the peer root
`subshift-elementary-mf-iff-word-edges-lie-on-cycles`.

## 0. Summary

- **(T1) Kazhdan collapse.** For a countable Kazhdan group Γ and ANY trace τ on C*_max(Γ):
  amenable ⟺ quasidiagonal ⟺ a weak* limit of normalized traces of finite-dimensional representations.
  The canonical trace τ_Γ has these properties iff Γ is residually finite. (This is Ozawa's Thm 7.4 plus
  definitions; the node packages it.)
- **(T2) Rings.** For a finitely generated unital ring R and n ≥ 3: τ_{EL_n(R)} is amenable ⟺ QD ⟺
  EL_n(R) is RF ⟺ R is a residually finite ring. Paradoxical rings (2n[1] ≤ n[1] in V(R), e.g. a full
  complementary idempotent) have no nonzero finite quotient rings, so their τ is never amenable. So is τ of
  every finitely generated simple infinite ring, matricial or not.
- **(T3) Candidate refuted.** "τ_{EL_n(R)} is QD iff R admits a faithful Sylvester rank function that is a
  limit of matrix ranks" is false: the Pestov ring LC(X,F_q)⋊Z has such a rank function and τ is not QD.
  The canonical QD trace is blind to paradox versus measure.
- **(T4) Corona traces.** Say τ on C*_max(G) is a *corona trace* if τ = tr_ω∘Φ for a unital *-homomorphism
  Φ into a norm matrix corona. Then τ_G a corona trace ⟹ G operator MF; G LEF ⟹ τ_G a corona trace; and for
  an infinite Kazhdan LEF group without finite quotients no realizing Φ admits a ucp lift.
- **(T5) Separation.** Paradoxical rings: every corona trace of C*_max(EL_N(R)), N ≥ 2n, is the trivial
  character. Matricial rings (unital subrings of ultraproducts of matrix algebras over finite fields):
  τ_{EL_N(R)} is a corona trace. Subshift rings, n ≥ 4: τ is a corona trace ⟺ EL_n(R_X) MF ⟺ R_X directly
  finite. So the trace invariant that sees the dichotomy is the corona trace, not the QD trace.
- **(T6) Reduced side.** For infinite Kazhdan G, the canonical trace on C*_r(G) is never amenable and
  C*_r(G) is never QD; what survives is stable finiteness and the MF question for C*_r, open on the
  matricial side (with a strong-convergence firewall).

## 1. Imports (verbatim, arXiv:math/0306067v2, read from the arXiv PDF page images, 2026-09-13)

- **Theorem 6.1** (p. 21): "For a trace τ on a C*-algebra A in B(H), the following are equivalent.
  (i) The trace τ extends to an A-central state φ on B(H), i.e., the trace τ extends to a state φ on B(H)
  such that φ(ax) = φ(xa) for every a ∈ A and x ∈ B(H). (ii) There is a net of ucp maps θ_i: A → M_{n(i)}
  such that τ(a) = lim_i tr_{n(i)}(θ_i(a)) and lim_i tr_{n(i)}(θ_i(ab*) − θ_i(a)θ_i(b)*) = 0 for every a, b
  in A. (ii') The trace τ is liftable, i.e., there is a *-homomorphism θ: A → R^ω with a ucp lifting
  θ̂: A → ∏R such that τ = τ_ω θ. (iii) The functional μ_τ is continuous w.r.t. the minimal tensor norm on
  A ⊗ Ā. (iv) The representation σ_τ is continuous w.r.t. the minimal tensor norm on A⊗Ā."
- **Definition 7.2** (p. 24): "We say a group Γ has the property (F) (the factorization property) if the
  trace τ on the full C*-algebra C*Γ, defined by τ(s) = δ_{1,s} for s ∈ Γ, is liftable."
- **Theorem 7.4** (p. 26): "Let τ be a trace on the full C*-algebra C*Γ of a group Γ with Kazhdan's property
  (T). Then, τ is liftable if and only if there is a sequence of *-homomorphisms π_n: C*Γ → M_{k(n)} such
  that τ(a) = lim_n tr_{k(n)} π_n(a). In particular, a group Γ with the properties (F) and (T) is residually
  finite."
- p. 26, before Thm 7.4: "infinite simple groups with Kazhdan's property (T) (for existence of such groups,
  see [Gr1]) do not have the property (F) as it was shown by Kirchberg [Ki3]". Section 7 assumes all groups
  countable and discrete. Kirchberg, Math. Ann. 299 (1994), p. 552: "A discrete group with property (F) and
  property T is residually finite" (quoted in `pestov91-literature-background-2026-09-13-part4.md`).
- Amenable trace = condition (ii) (Brown's memoir); by Thm 6.1 it is the same as liftable.

## 2. (T1) The Kazhdan collapse

**Theorem.** Let Γ be countable with property (T) and τ a trace on C*Γ = C*_max(Γ). TFAE:
(a) τ amenable; (b) τ quasidiagonal (ucp φ_n: C*Γ → M_{d_n}, ‖φ_n(ab) − φ_n(a)φ_n(b)‖ → 0, tr∘φ_n → τ
weak*); (c) τ = weak*-lim tr_{k(n)}∘π_n for *-homomorphisms π_n. Moreover τ_Γ satisfies them iff Γ is RF.

*Proof.* (c)⟹(b): *-homomorphisms are ucp and multiplicative. (b)⟹(a): |tr(x)| ≤ ‖x‖ turns operator-norm
multiplicativity into condition (ii) of Thm 6.1. (a)⟹(c): Thm 6.1 (ii)⟹(ii') and Thm 7.4. For τ_Γ:
if Γ is RF, enumerate Γ∖{e} = {g_1, g_2, …}, choose finite-index normal K_i ∌ g_i, put N_m = K_1∩…∩K_m and
π_m = λ_{Γ/N_m}∘quotient; tr π_m(u_g) = [g ∈ N_m] → δ_{g,e}, and density plus contractivity give weak*
convergence. Conversely (F)+(T) ⟹ RF is the last sentence of Thm 7.4. ∎

*Consequence.* STW Problem X(1) (amenable ⟹ QD) holds for every trace on the full C*-algebra of a Kazhdan
group. The manuscript's amenable non-QD trace (Main Theorem l.249) necessarily lives on a non-Kazhdan group,
as it does (W = W_0 ⋊ Z).

## 3. (T2) Elementary groups over rings

**Theorem.** Let R be a finitely generated unital ring, n ≥ 3, G = EL_n(R). TFAE: τ_G amenable; τ_G QD;
G RF; R residually finite (every r ≠ 0 avoids some finite-index two-sided ideal).

*Proof.* G is Kazhdan (Ershov–Jaikin-Zapirain), so by (T1) the first three are equivalent.
- R RF ⟹ G RF: for g ≠ 1 some entry r of g − 1 is nonzero; choose I of finite index with r ∉ I; the
  reduction G → GL_n(R/I) lands in a finite group and ḡ − 1 has the entry r̄ ≠ 0.
- G RF ⟹ R RF: for r ≠ 0 pick a finite-index normal N ∌ e_12(r). With I = lev(N), for fixed i ≠ j the set
  {a : e_ij(a) ∈ N} equals I (`elementary-root-kernel-equals-level`). I is additive, and for a ∈ I, b ∈ R,
  [e_12(a), e_23(b)] = e_13(ab) ∈ N and [e_12(b), e_23(a)] = e_13(ba) ∈ N, so I is a two-sided ideal.
  a ↦ e_12(a)N is additive with kernel I, so R/I embeds in the finite group G/N; r ∉ I. ∎

**Corollary A (simple rings).** If R is finitely generated, simple and infinite, τ_{EL_n(R)} is not amenable
(n ≥ 3). This covers L_{F_q}(1,2) and the Pestov ring LC(X,F_q)⋊Z alike.

**Corollary B (paradox passes to quotients).** If 2m[1] ≤ m[1] in V(R) for some m ≥ 1 (in particular if
ts = 1 and R(1−st)R = R), every nonzero quotient ring of R is infinite, so R is not RF and τ_{EL_n(R)} is
not amenable (R f.g., n ≥ 3). *Proof.* The relation passes to R/I by base change; for a finite ring Q,
Q^{2m} a direct summand of Q^m forces |Q|^{2m} ≤ |Q|^m, so Q = 0. (Full defect: in a finite ring t̄s̄ = 1
forces s̄t̄ = 1, so 1 − s̄t̄ = 0 generates Q, and Q = 0.) ∎

**Corollary C (refutation).** The Pestov ring R embeds unitally in ∏_ω M_{N_k}(F_q) (artifact §3.2), so
rk(x) = lim_ω rank Ψ_k(x)/N_k is a Sylvester matrix rank function (the axioms pass to limits). Its kernel
{x : rk(x) = 0} is a proper two-sided ideal, so rk is faithful since R is simple. But τ_{EL_3(R)} is not QD
(Corollary A). So a faithful matricial rank function does not give a QD canonical trace.

## 4. (T4) Corona traces

Let Q_d = ∏_k M_{d_k}/⊕_k M_{d_k}, and let ω be a free ultrafilter. Norm-null sequences have tr → 0, so
tr_ω([x_k]) = lim_ω tr_{d_k}(x_k) is a tracial state on Q_d. **Definition.** A trace τ on C*_max(G) is a
*corona trace* if τ = tr_ω∘Φ for some d, ω and unital *-homomorphism Φ: C*_max(G) → Q_d.
Equivalently, G has an operator-norm corona approximation whose normalized traces converge along ω to τ.
For τ_G this is clauses (1)+(2) of the GKMP notion of MF, without the reduced-norm clause (3)
(`gkmp-mf-is-trace-regular-not-bare-operator-mf`).

**Theorem.** (a) If τ_G is a corona trace then G is operator MF. (b) If G is countable and LEF then τ_G is
a corona trace. (c) If G is Kazhdan and τ_G = tr_ω∘Φ with Φ admitting a ucp lift, then G is RF. In
particular, for an infinite Kazhdan LEF group without nontrivial finite quotients, the *-homomorphism
realizing its canonical corona trace (from (b)) has no ucp lift.

*Proof.* (a) As in the proof of manuscript Thm l.1349: g ↦ Φ(u_g) is a corona homomorphism, and
Φ(u_g) = 1 forces τ_G(u_g) = 1, so g = e. (b) Exhaust G by finite windows B_k with partial embeddings
σ_k: B_k → F_k into finite groups (injective, multiplicative inside B_k). Put Θ_k(g) = λ_{F_k}(σ_k(g)) on B_k
and 1 elsewhere; each pair eventually lies in a window, so Θ = [Θ_k] is a homomorphism G → U(Q_d),
d_k = |F_k|, extending to Φ on C*_max(G). tr λ_{F_k}(h) = [h = e], and σ_k(g) ≠ e for g ≠ e eventually, so
tr_ω∘Φ agrees with τ_G on canonical unitaries, hence everywhere. (c) A ucp lift (φ_k) is asymptotically
multiplicative in operator norm, with tr∘φ_k → τ_G along ω. C*_max(G) is separable, so a subsequence converges
weak*; τ_G is QD, and (T1) gives RF. ∎

*Witnesses for (c).* G = EL_3(LC(X,F_q)⋊Z) and S = G/Z(G): infinite, Kazhdan, LEF, no finite quotients
(`lef-kazhdan-group-without-finite-quotients-exists`). This sharpens the lifting gap of
`mf-to-weak-qd-citation-has-unproved-lifting-step`: even with the right trace, the lift cannot exist.

## 5. (T5) The separation theorem

Let R be countable and unital.
- **(i) Paradox.** If 2m[1] ≤ m[1] in V(R) and N ≥ 2m, every homomorphism from EL_N(R) to an MF group is
  trivial (`stably-infinite-ring-elementary-groups-have-no-mf-quotient`). By Lemma
  `prop:mf-residual-calculus` so is every corona homomorphism, so every corona trace of C*_max(EL_N(R)) is
  the trivial character. For R ≠ 0, τ_{EL_N(R)} is not a corona trace.
- **(ii) Measure.** If R embeds unitally in ∏_ω M_{N_k}(F_{q_k}) with all fields finite, then GL_N(R) embeds
  in ∏_ω GL_{N N_k}(F_{q_k}), a countable subgroup of an algebraic ultraproduct of finite groups is LEF, and
  τ_{EL_N(R)} is a corona trace (§4(b)).
- **(iii) Subshift rings.** For a finite-alphabet subshift X, R_X = LC(X,F_q)⋊Z and n ≥ 4:
  τ_{EL_n(R_X)} is a corona trace ⟺ EL_n(R_X) MF ⟺ R_X directly finite. Proof: MF ⟹ LEF (peer root) ⟹
  corona trace (§4(b)) ⟹ MF (§4(a)).
- **(iv) Blindness of amenability.** On both sides of (i)/(ii), for finitely generated simple infinite R and
  n ≥ 3, τ is never amenable (§3).

## 6. (T6) The reduced side

- **Not amenable.** Apply Thm 6.1(i) to A = C*_r(G) ⊆ B(ℓ²G): an A-central extension φ of τ restricts to
  ℓ^∞(G), with λ(g)fλ(g)* = translate of f, so it gives an invariant mean. So τ on C*_r(G) is amenable only
  for amenable G, and never for infinite Kazhdan groups.
- **Not QD.** C*_r(G) QD forces G amenable (Rosenberg; recalled, not imported). TWW is silent: it needs
  nuclearity.
- **What survives:** stable finiteness (faithful trace) and the MF question.
  - Paradox side: C*_r(EL_n(R)) is not MF (manuscript Cor l.1038).
  - Matricial side: open (`directly-finite-subshift-el-n-reduced-cstar-is-mf`).
- **Firewall.** Regular representations of the finite LEF approximants never converge strongly to λ_G for
  non-amenable G. With S a finite symmetric generating set, ‖Σ_{s∈S} λ_{F_k}(σ_k(s))‖ = |S| (constant vector),
  while ‖λ_G(Σ_s u_s)‖ < |S| (Kesten). Any approach must pass to ℓ²_0-pieces, and property (T) supplies no
  uniform gap there because the approximants are not representations.

## 7. Open questions (landed as open claims)

- `directly-finite-simple-ring-el-n-trace-is-corona-trace`: for f.g. simple directly finite R and n ≥ 3, is
  τ_{EL_n(R)} a corona trace? Known in the subshift class. Firewalls:
  - operator-MF approximations need not control the trace. Tensor powers kill |tr| < 1 but not operator-large,
    HS-small deviations (cf. `corona-hs-radical-is-finite-residual`);
  - characteristic-0 matricial embeddings give linear, not unitary, models.
- `directly-finite-subshift-el-n-reduced-cstar-is-mf`, with the firewall of §6.

## 8. Checks and scope

- Imports read verbatim from the arXiv PDF of math/0306067v2 (pp. 21, 24, 26). Kirchberg's journal PDF was
  not fetched (Springer redirect); its p. 552 sentence is taken from the landed background artifact.
- Recalled, not imported: Rosenberg's theorem, Kesten's criterion, the Sylvester rank-function axioms and
  their closure under limits.
- Novelty: (T1) is Ozawa/Kirchberg restated. New here, as far as the graph and these sources show:
  - the ring-level equivalence (T2) and Corollaries B–C;
  - corona traces as the separating invariant (T4–T5).
  Not checked against literature beyond Ozawa's survey.
