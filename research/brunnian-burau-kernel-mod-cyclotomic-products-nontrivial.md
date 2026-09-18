---
rg: 2
id: brunnian-burau-kernel-mod-cyclotomic-products-nontrivial
kind: claim
title: "For every product F of cyclotomic polynomials avoiding Phi_3, some nontrivial Brunnian 4-braid has Burau matrix congruent to I mod F, so no fixed-modulus Moody certificate can prove the witness claim"
distinct_from:
  burau-minus-one-kernel-meets-brunnian-four-braids: that claim is the single case F = t+1; this claim covers every product of cyclotomic polynomials Phi_d with d != 3, to any multiplicity, and adds the uniform Moody obstruction
  parity-correcting-push-fails-for-a-brunnian-four-braid: that claim kills parity-clean intersection counts, which see only t = -1; this claim kills every certificate that reads Moody polynomials modulo a fixed cyclotomic product avoiding Phi_3
  brunnian-four-braids-have-five-strand-moody-witness: that claim is the existence of an exact witness; this claim shows that the witness cannot be detected modulo any fixed such F, and leaves that claim open
artifacts:
  - experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.py
  - experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.log
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

**OPEN** as stated (demoted 2026-09-18; see Attempts). Part 1 is proved. Part 2 is proved for
every **pure** `Γ`, in particular for all `Γ ∈ K_5`, which is the only case the "what this
kills" discussion and `brunnian-four-braids-have-five-strand-moody-witness` use; the quantifier
"every `Γ ∈ B_5`" is not established. The missing input is
`moody-congruence-holds-for-arcs-ending-at-alpha-endpoints`, now required by the route.

Let `F = ∏_{d ≠ 3} Φ_d^{m_d}` be any finite product of cyclotomic polynomials not divisible by
`Φ_3 = t² + t + 1`.

**Claim.**
1. **(Kernel mod `F`.)** There is `1 ≠ X_F ∈ Brun_4` with `ρ_4(X_F) ≡ I mod F·(t − 1)`.
2. **(Uniform Moody obstruction.)** For every `k ≥ 1`, every conjugate `Φ_0` of `X_F^k` in `B_4`,
   and every `Γ ∈ B_5` (in particular every `Γ ∈ K_5`), `𝕄_{f(Φ_0)·Γ} ≡ 𝕄_Γ mod F`. Notation is
   as in `brunnian-four-braids-have-five-strand-moody-witness`, and the congruence holds in both
   composition orders.

**What this kills.** Consider any certificate for `brunnian-four-braids-have-five-strand-moody-witness`,
or any other Moody-type witness for Brunnian 4-braids, that concludes `𝕄_{f(Φ_0)Γ} ≠ 𝕄_Γ` by
exhibiting a nonzero residue of the difference in `Z[t^{±1}]/(F)`, for one `F` fixed in advance
and independent of `Φ`, with `Φ_3 ∤ F`. Every such certificate fails at step "the residue is
nonzero" on `Φ = X_F`, whatever conjugate, power or push map it picks. The invariant is the
residue of `𝕄` modulo `F`. This class includes:
- parity-clean counts, which see `t = −1` only (`d = 2`, `m = 1`);
- evaluations at primitive `d`-th roots of unity for `d ≠ 3`, together with finitely many
  derivatives there;
- intersection data read in a finite cyclic cover of order `N` with `3 ∤ N`, that is modulo
  `t^N − 1`;
- all combinations of these, also after further reduction modulo a prime `p`.

A proof of the witness claim must therefore let the modulus depend on `Φ` (for instance
`F = ∏_{d | N} Φ_d` with `N` growing with the length of `Φ`), work exactly over `Z[t^{±1}]`, or
use `Φ_3`.

## Attempts

- 2026-09-18 (adversarial referee pass, outcome refuted as stated): **Part 2's quantifier over
  all of `B_5` is not established; the gaps lens decides.** Referee's reason, verbatim:
  - "Compiled status on current origin/main (21ed703eb) was ESTABLISHED via route
    brunnian-burau-kernel-mod-cyclotomic-products-nontrivial-proof [COMPLETE], sole prerequisite
    brunnian-four-braids-are-pseudo-anosov [ESTABLISHED] — so a review was owed.
  - WHAT HOLDS. Proof steps 1-4 (Part 1 of the claim) are correct and I re-verified them with an
    independent exact Laurent-polynomial implementation, going beyond the shipped script:
    P=(rho_4(Delta_3^2)-I)/(t^3-1) is idempotent with Phi_3*P integral, rho_4(T_k)=I+(t^{3k}-1)P,
    rho_4(T_d) = I mod Q_d and Phi_d | Q_d for d=1,2,4,5,6,7,12 (and Phi_3 does NOT divide Q_3, so
    the exclusion is genuinely needed), [T_d,b] has rho != I and = I mod (t-1)Q_d, and the
    two-step X=[T_7,[T_4,b]] satisfies rho = I mod (t-1)Phi_4*Phi_7. The shipped
    experiments/moody-witness-equivalence-2026-09-17/cyclotomic_jets.py reruns clean ('ALL CHECKS
    PASS: True', exit 0) and matches its log. The commutator-ideal lemma (step 2), Delta_4^2 =
    Delta_3^2 z, and the nontriviality argument (step 4: X commutes with z^k; X,z in the free
    group K_4; cyclic centralizer; delete p_1, where z has exponent sum 4, so u-bar has infinite
    order and X Brunnian forces q=0) all check out.
  - WHAT FAILS — step 5 of research/brunnian-burau-kernel-mod-cyclotomic-products-nontrivial-proof.md,
    third bullet: 'Theorem A of the artifact (§5, for any Gamma in B_5 and both orders) and Lemma
    3.1 give (1 - t^s)(M_{f(Phi_0)Gamma} - M_Gamma) in (F(t-1)).' Theorem A of
    research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md is indeed valid for
    all Gamma in B_5, but it is a statement about the intersection form I of loop classes, not
    about M. The bridge to M is Lemma 3.1 (§3), whose construction explicitly requires 'the circle
    is small enough to miss alpha' — i.e. the arc's terminal marked point p must not be p_1 or
    p_2, since alpha runs from p_1 to p_2 and any small circle about p_1 crosses alpha° exactly
    once. For Gamma in B_5 whose underlying permutation sends 3 to 1 or 2, the arc
    (beta_*^3)Gamma ends at p_1 or p_2 and that hypothesis is unsatisfiable. Concretely Lemma 3.1
    is then false: take A a simple arc from p_* to p_1 meeting alpha° nowhere, so M(alpha,A)=0
    while I([c~_A]) = ±t^{k_0} != 0 (the one crossing contributed by the small circle). Redoing
    the computation gives I([c~_A]) = (1-t^s)M_A + eps_0 t^{k_0}, and since the two arcs
    A=(beta_*^3)f(Phi_0)Gamma and B=(beta_*^3)Gamma generally sit over different sheets, the extra
    terms differ by eps_0 t^{k_0}(t^delta - 1), which is only in (t-1), not in (F(t-1)). So the
    mod-F conclusion does not follow for those Gamma, and Corollary 3.2 (well-definedness of M) is
    likewise unproved there.
  - SCOPE OF THE DEFECT. The claim's operative content is untouched: Part 1 stands, and Part 2
    stands for every pure Gamma, in particular for all Gamma in K_5 = pi_1(D_4,p_5), which is the
    only case the 'what this kills' section and brunnian-four-braids-have-five-strand-moody-witness
    use. The headline ('no fixed-modulus Moody certificate avoiding Phi_3 can prove the witness
    claim') therefore survives. But the compiled statement asserts 'every Gamma in B_5', and that
    quantifier is not established by the route. No other node depends on this claim, so the fix is
    to restrict Part 2 to pure Gamma (or Gamma in K_5) and re-land. Note the same over-broad
    quantifier is inherited from the artifact's Proposition 9.1 / Theorem B, i.e. it also affects
    the already-established parity-clean-arc-counts-see-only-burau-mod-t-plus-one and
    parity-correcting-push-fails-for-a-brunnian-four-braid.
  - Citations lens: the one external import (Artin's formula; MKS/Lyndon-Schupp cyclic centralizers
    in free groups) is used with correct hypotheses and direction. Calibration lens: the
    construction genuinely uses B_4-specific input (freeness of K_4 = ker(P_4 -> P_3),
    torsion-freeness of B_3, the idempotent P coming from Delta_3^2), and it correctly does not
    extend to Phi_3 (verified: rho_4([T_4,b]) is not = I mod Phi_3). The decisive lens is gaps."
  - **The exact step that fails.** Step 5 of the route, third bullet.
  - **Demotion.** The missing statement is now
    `moody-congruence-holds-for-arcs-ending-at-alpha-endpoints` (OPEN), added to the route's
    `requires:`. The proof file and the scripts are kept: everything else in them stands.
