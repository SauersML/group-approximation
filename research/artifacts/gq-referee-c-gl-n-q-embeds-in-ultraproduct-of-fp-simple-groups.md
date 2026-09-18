# Referee report (gq-referee-c): gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups

- **Node:** `research/gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups.md` and its `-proof` route, landed
  a6c28b163 by lane `gq-reform-countable`.
- **Lens:** independent re-derivation and calibration.
- **Verdict: PASS.** No changes needed.

## Re-derivation

- **Input.** `rational-linear-groups-satisfy-boone-higman` is an established literature import of Zaremsky,
  arXiv:2405.09722, Theorem 1.2: every finitely generated subgroup of `GL_n(Q)` embeds in a finitely presented
  simple group. It is the only input.
- **Clause 1.** Exhaust `GL_n(Q)` by `H_i = <g_1,…,g_i>` and let `ι_i : H_i -> K_i` be the embeddings. For any
  `g, h`, both lie in `H_i` for a cofinite set of `i`, and every nonprincipal ultrafilter contains that set. So
  `Φ` is a homomorphism. For `g ≠ 1`, `ι_i(g) ≠ 1` on a cofinite set, so `Φ` is injective. ✓
- **Clause 2.** A finite solution lies in some `H_i`. `ι_i` is an injective homomorphism, so it carries the
  equations and inequations to `K_i`. ✓
- **Clause 3.** Quantifier-free formulas are preserved and reflected by injective homomorphisms, and by passage
  to subgroups. So a universal sentence true in every `K_i` is true in each `H_i`, and hence in `GL_n(Q)`. ✓
  Clause 1 is the ultraproduct packaging of the same fact, a group lying in `ISP_U(K)` as its universal theory
  requires.
- **n = 1.** It holds too: every finitely generated abelian group embeds in `V`.

## Calibration

- **O1–O3.** Not engaged. An ultraproduct of finitely presented simple groups is neither finitely presented nor
  residually finite in general, and the claim puts `GL_n(Q)` in no residually finite group.
- **Distortion and FW.** Not relevant to a local statement.
- **What it does not say.** The node states this correctly. The uniformity step, one host for the ascending
  union, is the whole open content of the root. Per-subgroup methods reach only this claim.

## Remarks

- No novelty claimed, and none is due. The argument is the standard assembly of Zaremsky's theorem with Łoś.
