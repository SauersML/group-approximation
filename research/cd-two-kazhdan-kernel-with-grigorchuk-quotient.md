---
rg: 2
id: cd-two-kazhdan-kernel-with-grigorchuk-quotient
kind: claim
title: A finitely generated torsion-free group of cd 2 has a finitely generated Kazhdan normal subgroup whose quotient is the first Grigorchuk group, so amenability of the quotient alone cannot exclude infinite torsion quotients in dimension two
distinct_from:
  ollivier-wise-kazhdan-rips-construction: that is the general Rips-type construction; this applies it to one amenable torsion quotient and reads off which arguments for Kropholler's question in dimension two it kills
  cd-two-torsion-quotient-counterexamples-embed-in-out: that derives structure of a putative amenable example with infinite torsion quotient; this is a non-amenable example with the same shape, marking which parts of that structure need amenability of the kernel
  cd-two-group-with-infranormal-kazhdan-pair: that uses the Ollivier--Wise cover over a unit group to get compressed Kazhdan pairs; this uses it over the Grigorchuk group to get a torsion quotient
---

**ESTABLISHED** through `cd-two-kazhdan-kernel-grigorchuk-quotient-proof`, from
`ollivier-wise-kazhdan-rips-construction`, `grigorchuk-group-is-just-infinite-torsion-not-fp` and
`grigorchuk-hnn-extension-is-fp-amenable-non-ea`.

Let `𝔊` be the first Grigorchuk group. There is a short exact sequence `1 → N → Γ → 𝔊 → 1` with:

1. `Γ` finitely generated, torsion-free, with `cd Γ = 2`;
2. `N` finitely generated, infinite, with property (T), hence not amenable, and `cd N = 2`;
3. `Γ/N ≅ 𝔊` infinite, finitely generated, amenable, torsion and just-infinite;
4. `H_0(N; U(Γ)) = 0`, so the exact coinvariant formula
   `H_1(Γ; U(Γ)) ≅ V / Σ_i (1 − e_i) V`, with `V = H_1(N; U(Γ))`, holds verbatim. This is item 2 of
   `cd-two-torsion-quotient-counterexamples-embed-in-out`, whose proof of that item uses only
   `H_0(N; U) = 0`.

**What it kills.** Statement (A) of `cd-two-torsion-quotient-counterexamples-embed-in-out` says
that no finitely generated amenable group of cd 2 has a finitely generated normal subgroup with
infinite torsion quotient. Drop amenability of `G` but keep amenability of `G/N`, and (A) is false.
So every argument for (A) whose inputs are only

- `G` finitely generated, torsion-free, `cd G ≤ 2`,
- `N ⊴ G` finitely generated and infinite,
- `G/N` infinite, finitely generated, amenable and torsion,

proves a false statement, and is dead. This includes:

- vanishing of `L²`-Betti numbers and of `U`-coefficient cohomology of the amenable quotient (the
  Cheeger–Gromov input);
- the finite-cyclic averaging of item 2 in the target;
- the finite linear shadows of item 3;
- any Fox-Jacobian or rank-deficit count that sees `N` only through its finite generation.

The step where each fails: none of them uses amenability of `N` (equivalently of `G`). A proof of
(A) must use it. The only place the target uses it is the EA-radical theorem behind item 1
(`Z(N) = C_G(N) = 1`). A Kazhdan `N` is exactly what that theorem cannot see.

**Remark (not needed above; recalled, not re-checked).** Grigorchuk computed
`H_2(𝔊; Z) ≅ (Z/2)^∞`, so `𝔊` is not `FP_2`. Since a quotient of an `FP_2` group by a finitely
generated normal subgroup is `FP_2`, `Γ` is not `FP_2` either. This matches the profile of a
two-dimensional counterexample to Kropholler's question, which cannot be `FP_2`
(`amenable-fp-iff-affiliated-top-homology-vanishes`), except that `Γ` is not amenable.

**Left open.** Whether `H_1(Γ; U(Γ)) ≠ 0` here, that is, whether the coinvariants of item 4 really
survive. If `N` is `FP_2`, then `V = 0` and they vanish. So this node kills
non-existence arguments that forget amenability of `N`. It does not show that the coinvariant
route itself fails.
