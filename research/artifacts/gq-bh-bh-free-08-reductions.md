# bh-free-08 (free lane, seed: reductions), 2026-09-18

## 1. Survey of existing reductions (no new node)

Main already carries a dense web of equivalent forms of `boone-higman-conjecture`:
- simple Kazhdan FA inputs;
- fp just-infinite hosts;
- infinite computably presented simple inputs;
- local BH, which is equivalent to BH (`local-boone-higman-iff-boone-higman`), and CGP Question 4;
- the decidable-edge tower collapse;
- finitary permanence collapse;
- the logical form (Π_4, UBH);
- exactness separation.

Candidates I derived, and why none was landed:
- **Residually-fps form.** Every fp decidable group has a homomorphism to an fp simple group that is nontrivial on a chosen f.g. simple subgroup. This is the local-BH collapse restated.
- **Modular group.** Every decidable input is a quotient of `PSL_2(Z)` with recursive kernel. Trivial, since `F_2` works equally well.
- **Existentially closed groups.** BH holds iff, in some (equivalently every) countable existentially closed group `M`, every f.g. decidable subgroup lies in an fp simple subgroup of `M`. The proof uses amalgamation over the subgroup and the fact that a homomorphism from a simple group with one nontrivial image is injective. This is close to the compactness reformulation in `research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md` and does not change what must be proved.
- **One explicit universal input.** Impossible: `complexity-bounded-host-classes-are-not-universal` and Boone–Rogers rule it out.

## 2. Pivot: which finite germ extensions can Belk–Hyde–Matucci's cheap corollary certify?

- `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` (lane proof):
  - over the base `V`, Corollary 2.10 needs rational singular points (at irrational points `Fix_V(p)` is not f.g.);
  - it needs germ groups commuting with a power of the `V`-germ;
  - those centralizers are `C(C,Z) ⋊ V`;
  - so every certified host lies in an explicit group `V♯_{S,a}` whose word problem is in time `2^{O(l)}`.

  Hence Corollary 2.10 over `V` can never carry Boone–Higman, and Theorem 2.1 must be used at germs outside all such centralizers, as the shell route does.
- `cantor-cover-germ-extension-of-v-is-fp-simple` (lane proof): the ceiling is attained.
  - `V♯` is the full extension of `V` at the orbits of `0^∞` and `1^∞` by all `V`-germ-commuting germs.
  - It is finitely presented, via an explicit finite presentation of `(C(C,Z)/Z) ⋊ V`, and simple, via BHM Theorems 1.3/1.4 (perfect).
  - It contains the lamplighter `C(C,Z) ⋊ V`, realized globally as the `t`-commuting homeomorphisms of `C ∖ {0^∞,1^∞}` for the translation `t ∈ V`.
  - It contains `Q`, by odometer roots of `t`.

  This is the Cantor analogue of BHM's `VA`, and it recovers Q ⊆ fp simple as a calibration.

## 3. New route to Zaremsky Problem 1.25 (simple FP_2 envelopes)

- `bhm-singfix-finiteness-holds-for-type-fp-n` (check of the published argument): BHM Theorem 2.1 and Corollary 2.10 hold with `FP_n`.
- `every-countable-group-has-an-fp2-shell-envelope` (OPEN), with route `every-countable-group-embeds-in-simple-fp2-via-fp2-shells`. Perfect inputs make shell envelopes simple, so Problem 1.25 reduces to the `FP_2` version of the shell `SingFix` gate.
- That gate is strictly more flexible than the Boone–Higman one: the input can be any f.g. perfect group (no decidability) and the enumeration arbitrary. Necessary conditions are `A_1`, `Q_ν`, `F_ν` and `R_ν` of type `FP_2`.
- Not decided. The natural lever is Leary-type homological redundancy of the far relations.
