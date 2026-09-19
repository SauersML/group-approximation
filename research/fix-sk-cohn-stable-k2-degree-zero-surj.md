---
rg: 2
id: fix-sk-cohn-stable-k2-degree-zero-surj
kind: claim
title: "Fix the SK open row (tex l.733-735): discharge LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement"
---

**OPEN.** Every Lean route to census row 768ac9454e9b of `simple_kazhdan_sofic_group.tex`
(l.733-735, "Infinite finitely presented simple Kazhdan groups exist") takes a single owed Prop.
The Prop comes in three forms, and each is proved equivalent to the others:

- `LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`, the stable surjectivity of `K₂(C₀) → K₂(C)`,
  where `C = C_2(𝔽₂)` and `C₀` is its degree-zero part;
- stable `K₂(C_2(𝔽₂)) = 0` (`SKFix01.skFix01_degreeZeroSurj_iff_cohn`);
- `hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit` (`LVWire/Chain.lean`).

Conditional modules on main that take it, with no other owed input:

- `Full/LVWire/Chain.lean`;
- `Full/LVCohnColimit/Final.lean`;
- `Full/SKFix01/{CohnK2,Assembly,Wire,WireSentence}.lean`;
- `Full/LVAssembly/Endpoint.lean` and `Full/LVCohnK2/Final.lean`. These two stale drafts were repaired by lane ms-sk-uncond-a in 8bb2199cc2 and are unprobed while `SLURM-BLOCKED`.

Everything downstream of the Prop is proved: descent to `L_{𝔽₂}(1,2)`, superperfect units, `K₂(4, L) = ⊥`, finite presentation of `EL_5(L)`.

**What it needs.** The degree-two case of Ara–Brustenga–Cortiñas, *K-theory of Leavitt path
algebras*, Münster J. Math. 2 (2009), Thm 3.6. The Cohn algebra is a corner skew Laurent ring
`C₀[t₊, t₋; φ]`, and every `K₂` class of `C` comes stably from `C₀`. Proved inputs on main:

- `K₂(C₀) = 0`, since `C₀` is ultramatricial (`LVCohnColimit/CohnLimK2DegZero`);
- directed unions (`LVCohnK2/DirectedUnion`) and finite products (`LVCohnK2/Products`);
- Morita invariance (`LVCohnK2/Morita`);
- graded Steinberg words in `K₂(C)` are stably trivial (`LVCohnGraded/Vanishing`);
- untwisted `NK₂(S) = 0` for ultramatricial `S`, `NK₂(𝔽₂) = 0`, and stable `K₂(𝔽_p[x]) = 0`
  (`LVPolyK2/Basic`, which carries over `K₂(N, 𝔽_p[X]) = ⊥` from the Boone–Higman lane bh-met-94e).

Open sub-inputs of the ABC Step 3 route:

- the free-algebra base case, Gersten's `K₂(𝔽₂⟨x₀,x₁⟩) = K₂(𝔽₂)`. It is open as
  `LVFreeAlgK2.AugNilK2Trivial (freeAug (ZMod 2) (Fin 2))`, or via the stronger residual
  `LVFreeAlgGersten.skGer_PolyNilStatement`. Only the one-generator case is proved
  (`LVPolyK2.skPolyK2_augNil_freeAlgebra_one_zmodTwo`);
- the localization / Mayer–Vietoris step for `K₂` (Yao 1995, Thm 2.1; Quillen 1973 §5). It is open
  as `LVSkewLaurentK2.YaoFactorization`, twisted `NilK2Trivial`, or `LVK2Route` Core-A/Core-B.

The branch archive `tools/branch-archive/claude_great-ptolemy-7vplxg/` has no usable proof. Its
`LVCohnColimit/Final.lean` and `LVFreeAlgK2/Endpoint.lean` call lemmas that were never written
(`exists_cohnColimit_embedding`, `LVFreeAlgGersten.Endpoint`).

**Resolution.** When a producer of the Prop builds green with `#audit_closed_axioms`, change the
status line above to `**RESOLVED (<green commit>).**`.
