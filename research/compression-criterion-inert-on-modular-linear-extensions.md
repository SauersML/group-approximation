---
rg: 2
id: compression-criterion-inert-on-modular-linear-extensions
kind: claim
title: In a locally-finite-by-modular-linear group every compressed commuting factor of a Kazhdan group is finite, so the expander-matching criterion certifies no nonsofic subgroup of GL_n over a Jacobson algebra
distinct_from:
  openai-expander-matching-criterion: that is the criterion, concluding that the commuting factor is LEF if the ambient group is sofic; this proves, with no soficity hypothesis, that in the class LF-by-(char p linear) the commuting factor is finite, so the conclusion holds automatically and the criterion never produces a nonsofic group there.
  one-sided-compression-nonsofic-criterion: that is the formalized bridge on a CompressionSetup (J inside Gamma, centralized by a compressed copy of Gamma); the same finiteness theorem covers that packaging too, so the kernel-checked criterion is inert on the same class.
  openai-criterion-commuting-factor-is-central: that derives from soficity that the conjugated commuting factor is central in Gamma, hence abelian; this derives centrality in the symbol image without soficity and adds the positive-characteristic determinant step that makes it finite.
  compression-defects-die-in-rigid-targets: that kills the rigid defect in every linear target through a Zariski support, which is the first step here; this adds the central-eigenspace determinant lemma in characteristic p and the lift through a locally finite kernel, which turn centrality into finiteness of the factor itself.
  kazhdan-criterion-is-inert-on-finitary-permutation-extensions: that shows the normal-Kazhdan MF criterion is inert on Sym_fin extensions of MF groups; this shows the sofic expander-matching criterion is inert on locally-finite-by-modular-linear groups, a different criterion on a different class.
  jacobson-elementary-subgroups-are-locally-finite-by-linear: that is the structure theorem for EL_n(J) (locally finite symbol kernel, linear symbol image); this consumes it and kills a nonsoficity mechanism on it.
  binary-jacobson-el3-is-sofic: that is the open soficity question for E = EL_3(J); this removes the only packaged nonsoficity criterion from its negative side but decides nothing.
  kazhdan-compression-instances-have-infinite-vcd: that forces J'^m <= Gamma for all m and hence infinite vcd in instances; this forces J' finite in a whole ambient class, which is incompatible with any non-LEF instance.
artifacts:
  - research/compression-criterion-inert-on-modular-linear-extensions-proof.md
---

**ESTABLISHED** (route `compression-criterion-inert-on-modular-linear-extensions-proof`).

**Class MLE.** A group `X` is *locally-finite-by-modular-linear* if there are a field `k` of characteristic
`p > 0`, an integer `d`, and a homomorphism `rho : X -> GL_d(k)` with locally finite kernel. The class is closed
under subgroups.

**Theorem (MLE1).** Let `X` be in MLE. Let `Gamma <= X` have torsion abelianization (for example property (T)),
let `t in X` satisfy `t Gamma t^-1 <= Gamma`, and let `C <= Gamma` be finitely generated with
`[t Gamma t^-1, C] = 1`. Then `C` is finite.

**Corollary (MLE2, Proposition 2.3 packaging).** If `J' <= X` is finitely generated, `[Gamma, J'] = 1` and
`t J' t^-1 <= Gamma`, then `J'` is finite. (Apply MLE1 to `C = t J' t^-1`.) `Gamma cap J' = 1` is not used.

**Corollary (MLE3, CompressionSetup packaging).** If `J <= Gamma` is finitely generated and a compressed copy
`q Gamma q^-1` centralizes `J`, then `J` is finite.

**Corollary (MLE4, Jacobson class).** Let `F` be a finite field, `J_F = F<S,T | TS = 1>`, `n >= 1`. Every subgroup
of `GL_n(J_F)` is in MLE, with `rho` the symbol map to `GL_n(F(x))` and kernel `GL_n(J_F, I)`, `I = (1 - ST)`.
So no compression triple inside any subgroup of `GL_n(J_F)` has an infinite commuting factor.

## Obstruction (class killed)

**Class.** Every proof that a group `Y` is nonsofic by exhibiting a compression triple `(Gamma, t, J')` in `Y`
with `J'` not LEF: the OpenAI Proposition 2.3 in both versions, and the kernel-checked
`not_isSofic_of_not_isLEF`. A nonsofic subgroup must be certified by a triple lying inside `Y`, so the class dies
for every `Y` in MLE. This includes `E = EL_3(J)`, `Gamma_T = EL_5(J)`, `EL_20(J)` and every subgroup of
`GL_n(J_F)`.

**Invariants.** (i) the Zariski closure `H` of `rho(Gamma)`, which conjugation by `rho(t)` preserves
(same dimension and component count); (ii) the determinant of the centralizing factor on each eigenspace of its
semisimple part, which is `1` on the derived subgroup and is a power of the eigenvalue.

**Death step.** The step where a triple would supply a non-LEF witness. MLE1 forces the witness to be finite, and
finite groups are LEF. The conclusion of the criterion is automatically true, so it certifies nothing.

**What survives.** Only the rigid-defect criterion `sofic-groups-kill-rigid-compression-defects` with a defect
lying in the locally finite kernel and a Kazhdan compressor hull. In `GL_n(J_F)` the natural corner compressor
`u = [[S, Q], [0, T]]` has a nontrivial defect in `GL_n(J_F, I)`, but its hull is not Kazhdan: the top-block
determinant of the symbol is a character that is trivial on `Gamma` and sends `u` to `x^m`, of infinite order. See the route's closing remark.

## Scope

- Characteristic `p > 0` is used. In characteristic `0` a central unipotent in the derived subgroup can have
  infinite order, and MLE1 is not claimed.
- Nothing is said about soficity of any group in MLE. The binary Leavitt head is not in MLE (the Leavitt unit
  group contains `V`), which is consistent with `openai-leavitt-unit-nonsofic`.
