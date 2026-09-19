---
rg: 2
id: bounded-depth-symmetric-models-are-sofic-approximations
kind: claim
title: Hyperlinear models through bounded-depth representations of symmetric groups are sofic approximations, so they see the Jacobson head only if EL_5(J) is sofic
artifacts:
  - experiments/bounded-depth-symmetric-models-2026-09-18/check_char_asymptotic.py
  - experiments/bounded-depth-symmetric-models-2026-09-18/output.txt
distinct_from:
  jacobson-head-concentrates-on-template-constituents: that shows the head of a finite-group model lives on template constituents, where every relator is nearly but not exactly scalar; this treats the symmetric-group constituents of bounded depth, which are template constituents, and shows a model carried by them is a sofic approximation in disguise.
  jacobson-head-dies-in-gapped-finite-group-models: that kills models through groups with a uniform character-ratio gap; symmetric groups have no gap (a transposition has ratio 1 - 2/(m-1) in the standard representation), and here the head is not killed but reduced to soficity of EL_5(J).
  template-constituents-primitive-or-small-minimal-degree: that pushes induced template constituents down to primitive permutation groups of vanishing relative minimal degree; this is the next step for the alternating case of bounded depth, converting a Hilbert-Schmidt model into a Hamming one.
  fp-simple-models-concentrate-on-template-constituents: that states the permutation template for sofic models of finitely presented simple groups; this goes the other way, from unitary models through symmetric-group representations back to permutation models, for any group.
  binary-jacobson-el3-is-sofic: that is the open soficity question in rank three; this shows that bounded-depth symmetric certificates for the head of St_20(L_(F_2)(1,2)) exist only if the rank-five analogue, which implies it, holds.
---

**ESTABLISHED** (route `bounded-depth-symmetric-models-are-sofic-approximations-proof`, swarm-0917-w14-w14-nh-pull, 2026-09-18, unreviewed).

**Setting.** A *symmetric model of depth at most `D`* of a group `G` is a sequence
`π_k(g) = c_k(g) ρ_k(φ_k(g))`, where
- `φ_k : G -> Sym(m_k)` is an arbitrary map, with `m_k -> ∞`;
- `c_k : G -> U(1)` is an arbitrary scalar cochain;
- `ρ_k` is a unitary representation of `Sym(m_k)`. Each irreducible constituent `S^λ` is one-dimensional, or has
  `1 <= m_k - λ_1 <= D`, or has `1 <= m_k - λ'_1 <= D`.

The defect is `def_F(π_k) = max_{g,h in F} ||π_k(g)π_k(h) - π_k(gh)||_2`, in the normalized Hilbert-Schmidt norm. The
model is asymptotic if `def_F(π_k) -> 0` along an ultrafilter `ω` for every finite `F`. Let `w_k` be the total weight
(normalized dimension) of the constituents of dimension `> 1`. Models through `A_m` of bounded depth are the case
`φ_k(G) ⊂ Alt(m_k)`. They include the permutation actions of `A_m` on configurations of at most `D` points.

**Lemma CA (character asymptotic).** For each `j >= 1` there is `C_j`, and for `m >= 4j`, every `μ ⊢ j` and every
`σ ∈ Sym(m)` with `F(σ)` fixed points,
```text
| χ^{(m-j,μ)}(σ) / dim S^{(m-j,μ)}  -  (F(σ)/m)^j |  <=  C_j / m .
```

**Theorem A.** Let `π_k` be an asymptotic symmetric model of depth `<= D` of any group `G`, and suppose
`lim_ω w_k = w > 0`. Then for all `g,h ∈ G`,
```text
d_Ham(φ_k(g)φ_k(h), φ_k(gh))  <=  def_{g,h}(π_k)^2 / w_k  +  C_D / m_k   ->  0 .
```
So `(φ_k)` is a sofic approximation of `G`. It need not be separating. Its sofic trace `τ_s(g) = lim_ω Fix(φ_k(g))/m_k`
has kernel `N_s = {τ_s = 1}`, a normal subgroup, and `G/N_s` is sofic. For a commutator `z = [a,b]`,
```text
||π_k(z) - 1||_2  <=  4 def_F(π_k)  +  ( 2 w_k ( D (1 - Fix(κ_k)/m_k) + C_D/m_k ) )^(1/2)
```
for a finite set `F` containing `a, b, z, ab, ba, zb` (`zba = ab`),
with `κ_k = [φ_k(a), φ_k(b)]`, and `d_Ham(φ_k(z), κ_k) -> 0`. Hence `lim_ω ||π_k(z) - 1||_2 > 0` forces `w > 0` and
`τ_s(z) < 1`.

**Corollary B (the head).** Let `J = F_2<S,T | TS=1>`, `Q = 1-ST`, and let `E_n = EL_n(J)` for `n >= 3`, with head
`z_Q = x_13(Q) = [x_12(Q), x_23(1)]`.
- If some asymptotic symmetric model of bounded depth of `E_n` has `lim ||π_k(z_Q) - 1||_2 > 0`, then `E_n` is
  sofic. Conversely, if `E_n` is sofic, then composing a sofic approximation with the standard representation
  (`D = 1`) gives such a model.
- For `Δ = St_20(R)`, `R = L_(F_2)(1,2)`, and its head `z = x_13(s_1t_1)`: if a bounded-depth symmetric model of `Δ`
  sees `z`, then `EL_5(J)` is sofic, and hence so is `EL_3(J)`. This uses the pullback along
  `EL_5(J) ≅ St_5(J) -> St_20(J) -> St_20(R)`, with `S -> s_2`, `T -> t_2`.

**Uniformity in depth.** There is a universal unbounded function `h` with the following property. With
`D = D_k <= h(m_k)`, the Hamming bound and the soficity of `G/N_s` in Theorem A still hold, with error term
`m_k^{-1/2}`. So does the commutator bound, with `D_k` in place of `D`. The head conclusions (the last sentence of
Theorem A, and Corollary B) additionally need `D_k · d_Ham(κ_k, 1) -> 0` whenever `τ_s(z) = 1`. This holds
automatically for bounded depth.

**Numerical check.** Murnaghan-Nakayama characters, computed independently of the proof, give
`max m·|r - f^j| <= 1.72` for all `μ ⊢ j <= 3`, `16 <= m <= 96`, over 300+ cycle types
(`experiments/bounded-depth-symmetric-models-2026-09-18/output.txt`).

**What this kills (for `agent-leavitt-not-bcs-negative-root-corner`).** It closes the step named at the end of the
template-concentration entry: test the head against `A_m` acting on configurations of the Toeplitz truncation. For
configurations of bounded size, the test is exactly the soficity of `EL_5(J)`. So these certificates cannot refute
the hole by showing `EL_20(J)` is hyperlinear but not sofic. Any such refutation through finite groups must put its
head mass somewhere else:
- on symmetric constituents whose depth grows faster than `h(m)`;
- on growing depth `D_k <= h(m_k)`, where the head is invisible to the sofic trace but still moves a fraction
  `>= c/D_k` of points;
- on product actions of `A_m^ℓ` with `ℓ -> ∞`;
- or on the primitive non-alternating branch of `fp-simple-finite-group-models-reduce-to-alternating-constituents`.

**Invariant and death step.** The invariant is the fixed-point fraction `f`. On a constituent of depth `j`, the
character ratio is `f^j + O(1/m)`. The Hilbert-Schmidt defect of a relator is therefore at least
`w (1 - f) - O(1/m)`, which is a Hamming defect. The model dies as a non-sofic certificate exactly there.
