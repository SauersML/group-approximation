---
rg: 2
id: sl-2-z-localized-has-fp-hecke-overgroup
kind: claim
title: For some prime l, SL_2(Z_(l)) lies in a finitely presented group in which the Hecke correspondence at l extends to finite-index subgroups
distinct_from:
  rational-iwahori-group-lies-in-fp-self-similar-group: that asks for a finitely presented self-similar overgroup of the rational Iwahori group (the image in PGL_2(Q) of the Iwahori subgroup of GL_2(Z_(p))) on the p-ary tree, feeding a Rover--Nekrashevych host for PSL_2(Q); this asks for any finitely presented overgroup of SL_2(Z_(l)) in which the Hecke conjugation extends, feeding an HNN extension covered by Bux--Llosa Isenrich--Wu and reaching SL_2(Q) with its centre.
  sl-2-q-embeds-in-fp-simple-group: that is the embedding of SL_2(Q) itself; this is a statement about finitely presented, necessarily residually finite, overgroups of the vertex group SL_2(Z_(l)), and it implies that one via sl-2-q-via-hecke-overgroup-and-bliw.
  aff-n-z-localized-lies-in-fp-self-similar-group: that asks for a finitely presented self-similar overgroup of the affine group; this asks for any finitely presented overgroup, plus the extension of one partial isomorphism.
  bh-embeddability-survives-decidable-edge-hnn: that is a general permanence statement for HNN extensions over finitely generated edges; this replaces the non-finitely-generated edge group Γ_0(l) by a finite-index subgroup of a finitely presented group, where Bux--Llosa Isenrich--Wu apply.
---

**OPEN.** Notation of `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell`: `A = SL_2(Z_(l))`,
`α = diag(1, l)`, `Γ_0(l)` (lower-left entry in `l Z_(l)`) and
`Γ^0(l) = α^-1 Γ_0(l) α` (upper-right entry in `l Z_(l)`).

**Statement.** There are a prime `l`, a finitely presented group `Λ`, an
injective homomorphism `ι: A -> Λ`, subgroups `C_1, C_2` of finite index in `Λ`
and an isomorphism `φ: C_1 -> C_2` such that
- (H1) `ι^-1(C_1) = Γ^0(l)`;
- (H2) `ι^-1(C_2) = Γ_0(l)`;
- (H3) `φ(ι(y)) = ι(α y α^-1)` for every `y in Γ^0(l)`;
- (H4) some nontrivial group in the Bux--Llosa Isenrich--Wu class `BS_Λ` acts
  faithfully on its Bass--Serre tree, for example the HNN extension `Λ *_φ`.

**What any witness must look like.**
- **Residually finite.** By (H4) some group in `BS_Λ` acts faithfully on a locally finite tree. Its vertex
  stabilizers are residually finite and commensurable with `Λ`, so `Λ` is
  residually finite. This matches the remark after BLIW Theorem C that its base
  groups must be residually finite. In particular (H1)–(H4) never use the
  divisibility of `(Q,+)` at `l`, which O1 of `gl-n-q-embeds-in-fp-simple-group`
  forbids in residually finite groups.
- **Non-linear.** `Λ ⊇ Z_(l) ⊇ Z[1/P]` for `P` the primes other than `l`, so by
  `infinite-prime-localizations-embed-in-no-fg-linear-group` it is not a
  finitely generated linear group.
- **Residually finite overgroups of `A` exist, but not finitely presented ones.**
  `A` is residually finite and acts self-similarly on the `l^2`-ary tree
  (`aff-n-over-z-localized-at-ell-is-rf-and-self-similar`). No finitely presented
  residually finite overgroup is known; that is the content of this claim together
  with (H3).
- **The finite analogue holds.** For one prime `p` and `A_0 = SL_2(Z)`, the data
  `Λ = SL_2(Z)`, `C_1 = Γ^0(p)`, `C_2 = Γ_0(p)`, `φ` = conjugation by `diag(1,p)`
  satisfy (H1)–(H3). They are the data of Serre's
  `SL_2(Z[1/p]) = SL_2(Z) *_{Γ_0(p)} SL_2(Z)^{diag(1,p)}`. The claim asks for the
  same configuration with `Z` replaced by the ring `Z_(l)`, in which all primes
  but `l` are inverted.

## Attempts

None yet. Natural candidates for `Λ`:
- finitely presented self-similar groups containing `Aff_2(Z_(l))`
  (`aff-n-z-localized-lies-in-fp-self-similar-group`), where (H3) is then an
  extra requirement;
- residually finite groups built by HNN extensions over finite-index subgroups,
  in the style of the Burger--Mozes and BLIW constructions.
