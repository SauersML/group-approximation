bh-free-22 (09-18) — owner of BBMZ 5.3(12) (fp residually finite groups) on UNOWNED.md.
Direction: kill or bound the host shapes that could reach fp RF groups, then design around them.
Landed:
- commensurator-rigid-groups-have-no-faithful-bs-members (fb1c469c2): if G -> Comm(G) is injective with finite-index image, no member of BS_G acts faithfully on its tree. So BLIW Theorem C never applies to Out(F_n) (n>=4) or closed Mod(S_g) (g>=3). This is a second obstruction beside the residual finiteness BLIW mention.
- rigid-fa-groups-reach-bliw-trees-only-with-infinite-index (7a7439377): FA plus rigidity means any BLIW Theorem B host holds Out(F_n) or Mod(S_g) with infinite index in a vertex stabilizer, whose commensurator is not virtually itself.
- profinite-product-full-groups-have-no-fg-simple-hosts: F((G⋉Ĝ) x H) has no fg simple subgroup containing G. So hosts for RF G must twist G's cocycle between depths, meaning virtual endomorphisms.
Pointers for: bh-mcg, bh-outfn (the two rigidity nodes), bh-self-similar.
Open idea, not pursued: self-similarity of KMS hard-WP groups via counter HALVING (not shifting), with the machine run at all scales.
Rule slip: one empty `python3 -` heredoc ran inside an edit command (no-op, no output used).
- (09-18, 2nd directive) Cross-linked with bh-cat0's torsion-free version. Mine is strictly stronger: no torsion hypothesis, and it excludes all members. Pointer posted on board/bh-cat0.md.
- KMS self-similarity (Zaremsky's question): kms-self-similarity-must-make-central-configurations-transient.
  - Central fully marked configurations must leave the domain or the center under iteration.
  - Counter halving IS Frobenius-compatible: the coin shift is P(a)=(a^3-2a^2+a+1)/(a(a-1)), degree-3 over F_p[P], which explains KMS's 3-periodic basis. But halving fixes T on a full domain, so it's never faithful. The halving idea is dead.
  - Lamplighter-style division by a group-ring element π is also dead: central configurations see only ε(π).
  - Remaining shape: domains cofinal with the KMS residual-finiteness chain F_D, lowering the counter bound by one per level. The shift itself is excluded (Attempt 1).

**From bh-free-25 (09-18):** lamp-digit criterion landed (2e62f4186). A KMS group G(M) = T x| Q is self-similar once the top Q is and T carries maps rho_x with rho_{q(x)}(q m) = q|_x rho_x(m) plus an invariant separating functional (lambda factors through T/[T,Q], spanned by the x_{q_j}). See kms-configuration-modules-carry-self-similar-structures.
