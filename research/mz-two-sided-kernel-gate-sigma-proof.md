---
rg: 2
id: mz-two-sided-kernel-gate-sigma-proof
kind: route
title: The antitwisted fiber product is the kernel of eta+eta on R x R; the Bieri-Geoghegan product formula over Z in dimension two and Renz's kernel criterion force both eta and -eta into Sigma^1
target: mz-envelope-fp-forces-two-sided-fg-near-index-kernel
requires:
  - mz-envelope-germ-group-is-an-antitwisted-fiber-product
  - shell-germ-group-has-index-two-fiber-product
  - square-spiral-z2-near-shift-group-is-not-finitely-presented
artifacts:
  - research/artifacts/boone-higman-mz-antitwisted-germ-gate-2026-09-17.md
---

## Literature imports

All quotations are verbatim up to typesetting.

**(I1) Renz, Satz C.**

- Source: M. Ershov and M. C. B. Zaremsky, arXiv:2505.18826, §2, Theorem 2.3. Read 2026-09-17 from the arXiv LaTeX
  source `FINAL_VERSION.tex`, SHA-256 `52c1ddc9a381aa12336341a83561d730654689c5c9933dc4983aa7c54cf11f87`. This is
  the same import as `antipodal-sigma-pair-type-f-proof`.
- Theorem: "Let $G$ be a group of type $\F_n$ and $H$ a subgroup of $G$ containing the commutator subgroup $[G,G]$.
  Then $H$ is of type $\F_n$ if and only if $[\chi]\in\Sigma^n(G)$ for all $0\ne \chi \in \Hom(G,\R)$ such that
  $\chi(H)=0$."
- Discrete case: "if $0\ne \chi\colon G\to\R$ is \emph{discrete}, meaning its image is cyclic, then $\ker(\chi)$ is
  of type $\F_n$ if and only if $[\chi],[-\chi]\in\Sigma^n(G)$."
- Normalization: "homological BNSR-invariants $\Sigma^m(G,R)$ ... with $\Sigma^1(G,\mathbb Z)=\Sigma(G)$ ... and
  homotopical BNSR-invariants $\Sigma^m(G)$ ... with $\Sigma^1(G)=\Sigma(G)$".

**(I2) Bieri–Geoghegan, arXiv:0808.0013v2.** Read from `product21.tex`, SHA-256
`7eb4155df547c21c935a3ebd7254532e96b228944fdb853cf0aa14288af98e90`, the same file as
`characters-living-on-m-plus-one-factors-meinert-citation`. Theorems are numbered by section.

- Join: "when $P\subseteq S(G)$ and $Q\subseteq S(H)$ their {\it join} is $$P*Q:=\{[\chi +\chi ']\: |\:[\chi]\in P,
  [\chi ']\in Q\}\cup P\cup Q$$".
- Definition and convention: "$$\Sigma ^{n}(G;R):=\{[\chi ]\in S(G)\: |\:R\text{ is of type } FP_{n}\text{ over }
  RG_{\chi }\}$$", and "When we discuss $\Sigma^n(G;R)$, {\it we will always assume} that the group in question
  has type $FP_{n}(R)$."
- Theorem 1.1: "$$ \Sigma^n(G\times H)= (\Sigma^n(G\times H;\BZ)-(S(G)\cup S(H)))\cup (\Sigma^n(G)\cup \Sigma^n(H))
  $$". It is attributed there to Meier–Meinert–VanWyk, with a proof in Bieri's survey, Proposition 4.6.
- Direct Product Formula: "$$ \Sigma^n(G\times H;R)^c =\bigcup^n_{p=0} \Sigma^p(G;R)^c * \Sigma^{n-p} (H;R)^c$$".
- Theorem 1.2 (Meinert's Inequality), homotopical half: "$$ \Sigma^n(G\times H)^c \subseteq \bigcup^n_{p=0}
  \Sigma^p(G)^c *\Sigma^{n-p} (H)^c$$".
- Theorem 1.5 (label `Thm3`): "The Direct Product Formula is true when $R=\BZ$ provided $n\leq 3$." Its proof is
  explained in Remark 5.3 (label `rational`; numbering computed from the source counters): "the cases where both sides of the join are non-empty the dimensions
  of the relevant cycles are 0 and 1, and the 0-cycle can always be chosen to be indivisible."
- Characters on a product are written `χ+χ′`, and `S(G)`, `S(H)` are subspheres of `S(G×H)`, as recorded in the
  Meinert citation node.

## Derivation

Put `G = R × R` and `ψ(a,b) = eta(a) + eta(b)`. Then `ψ` is discrete with image `Z`, since `eta(s) = 1`. So
`ker ψ = F^-` contains `[G,G]`. The characters `eta∘pr_1` and `eta∘pr_2` are written `eta+0` and `0+eta`.

**Remark (uniqueness of components).** `Hom(G,R) = Hom(R,R) ⊕ Hom(R,R)`. So if `[ψ] = [χ+χ′]` or `[−ψ] = [χ+χ′]`,
then `χ` and `χ′` are the same positive multiple of `eta` (respectively of `−eta`). In particular `[±ψ]` is not in
`S(R×1) ∪ S(1×R)`.

**(⇒) Suppose `F^-` is finitely presented.**

1. By item 4 of `mz-envelope-germ-group-is-an-antitwisted-fiber-product`, `R` is finitely presented. So `G` is
   finitely presented, and every invariant below is defined.
2. By (I1) with `n = 2`, `[ψ], [−ψ] ∈ Σ^2(G)`.
3. By Theorem 1.1, the points of `Σ^2(G)` outside `S(R×1) ∪ S(1×R)` lie in `Σ^2(G;Z)`. So `[±ψ] ∈ Σ^2(G;Z)`.
4. Suppose `K` is not finitely generated. By (I1) with `n = 1` and `G = R` (type `F_1`), there is `ε ∈ {±1}` with
   `[ε eta] ∉ Σ^1(R) = Σ^1(R;Z)`.
5. By the join definition, `[εψ] = [ε eta + ε eta]` lies in `Σ^1(R;Z)^c * Σ^1(R;Z)^c`. This is the `p = 1` term of
   the right-hand side of the Direct Product Formula with `n = 2`.
6. By Theorem 1.5 (`R = Z`, `n = 2 ≤ 3`), that right-hand side equals `Σ^2(G;Z)^c`. So `[εψ] ∉ Σ^2(G;Z)`,
   contradicting step 3. Hence `K` is finitely generated.

**(⇐) Suppose `R` is finitely presented and `K` is finitely generated.**

1. By (I1) with `n = 1`, `[eta], [−eta] ∈ Σ^1(R)`.
2. If `[ψ'] ∉ Σ^2(G)` for `ψ' = ±ψ`, then Meinert's Inequality places `[ψ']` in some `Σ^p(R)^c * Σ^{2−p}(R)^c`.
3. By the Remark, `[ψ']` is a genuine sum `[χ+χ′]` with `[χ] = [χ′] = [±eta]`. Since `Σ^0 = S`, this needs `p ≥ 1` and
   `2−p ≥ 1`, so `p = 1` and `[±eta] ∉ Σ^1(R)`, which contradicts step 1.
4. So `[±ψ] ∈ Σ^2(G)`, and (I1) with `n = 2` makes `F^-` of type `F_2`, that is, finitely presented.

By item 2 of the germ claim, `Q = E/FSym` is finitely presented iff `F^-` is. This gives the displayed equivalence.

**Window form.** Each `W_N` is finitely generated, and `K = ∪ W_N` is an ascending union. So `K` is finitely generated
iff `K = W_N` for some `N`. If `s W_N s^-1 = W_N`, then `W_N` contains every `s^i lambda(P) s^-i`, hence equals `K`.
Conversely, if `W_N = K` then `s W_N s^-1 = W_N`.

**Consequence 1.** This is item 1 of the germ claim together with (⇒). The index-2 `H_2` inside `E_2` is recorded there.

**Consequence 2 (MZ gate ⇒ shell gate).**

- Let `E_nu(P)` be finitely presented. Then `R` is finitely presented and `[±eta] ∈ Σ^1(R)`.
- The symmetric product `F_nu = {eta(a) = eta(b)}` is `ker ψ⁺` with `ψ⁺ = eta + (−eta)`, again discrete onto `Z`.
- The argument of (⇐), with components `[±eta]` and `[∓eta]`, gives `[±ψ⁺] ∈ Σ^2(G)`, so `F_nu` is finitely presented.
- By `shell-germ-group-has-index-two-fiber-product` ("Q is finitely presented if and only if F_nu is"), the shell
  germ group is finitely presented.

**Consequence 3 (transferred kills).**

- **Square spiral.** For the square spiral enumeration, `R_nu` is not finitely presented by
  `square-spiral-z2-near-shift-group-is-not-finitely-presented`. That node uses the same `R_nu`: regular action
  transported along `nu`, with cofinite shift. So `E_nu(Z^2)` is not finitely presented.
- **Free products.** If `P*<s> -> R_nu` is injective and `P ≠ 1`, then `R ≅ P*Z` and `eta` is the exponent sum in
  `s`. Its kernel is the free product of the conjugates `s^n P s^-n` for `n ∈ Z` (Reidemeister–Schreier, or
  Bass–Serre on the line). This is not finitely generated: a finite set lies in finitely many factors, and so does
  the subgroup it generates. So `E_nu(P)` is not finitely presented. The hypothesis is the one of
  `free-shift-shell-envelopes-are-not-finitely-presented`; that node is not used in this argument.
- **One-sided cases.** If exactly one of `[±eta]` lies in `Σ^1(R)`, the equivalence fails. QED
