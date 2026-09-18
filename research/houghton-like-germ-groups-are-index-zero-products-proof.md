---
rg: 2
id: houghton-like-germ-groups-are-index-zero-products-proof
kind: route
title: Read off ray germs of H_n(G) as index-zero tuples in the extended germ group, then apply Meinert's inequality over at least three living factors and Renz's kernel criterion
target: houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
requires:
  - houghton-like-groups-are-strongly-shift-similar
  - mz-envelope-germ-group-is-an-antitwisted-fiber-product
  - characters-living-on-m-plus-one-factors-lie-in-sigma-m
  - regular-enumerations-can-make-near-shift-free-product
  - half-finite-generators-with-e2-are-strongly-shift-similar
---

Lane proof, not independently reviewed. Notation as in the target.

## Imports

- **(I1) Renz's kernel criterion, discrete case.** This is the import used in `mz-two-sided-kernel-gate-sigma-proof`:
  Ershov–Zaremsky arXiv:2505.18826, Theorem 2.3, read from the LaTeX with SHA-256 `52c1ddc9a381aa12336341a83561d730654689c5c9933dc4983aa7c54cf11f87`. Quoted there:
  "if $0\ne \chi\colon G\to\R$ is \emph{discrete} ... then $\ker(\chi)$ is of type $\F_n$ if and only if
  $[\chi],[-\chi]\in\Sigma^n(G)$", for `G` of type `F_n`.
- **(I2) `characters-living-on-m-plus-one-factors-lie-in-sigma-m`** (refereed). A character of a product of
  `k >= m+1` groups of type `F_m` that is nonzero on every factor lies in `Σ^m`.
- **(I3) Retracts.** If `r : A -> B` has a section `i` and `A = <X | S>` is finite, then
  `B ≅ A / <<x^-1 i(r(x)) : x in X>>`, so `B` is finitely presented.
  *Proof.* Call the normal closure `M`. Then `M <= ker r`. In `A/M` every `x ≡ i r(x)`, so every `g ≡ i r(g)`,
  and `r(g) = 1` forces `g ≡ 1`.

## Step 1. The extended germ group

- `psi_j(g) = s_{g(j)}^{-1} ∘ g|_{N\{j}} ∘ s_j`, and each `s_j` agrees with `n -> n+1` off a finite set. So
  `psi_infinity(ḡ) = s̄^-1 ḡ s̄`.
- Shift-similarity puts this in `Germs(G)`. Strong shift-similarity (Definition 3.17) makes `psi_infinity`
  onto, so `s̄^-1 Germs(G) s̄ = Germs(G)`.
- Elements of `Germs(G)` are classes of genuine permutations, so they have index 0, while `eta(s̄) = 1`.
- Hence `Ĝ = Germs(G) ⋊ <s̄>`, `Ĝ ∩ ker eta = Germs(G)`, and every element of `Ĝ` is `s̄^c ḡ` with `c = eta`.

## Step 2. Item 1, germs of H_n(G)

By Definition 4.1, an element of `H_n(G)` is given by arbitrary finite sets `M_+`, `M_-` with `|M_+| = |M_-|`, an
arbitrary bijection `σ : M_+ -> M_-`, and arbitrary `g_1, ..., g_n in G` (referee a, N1). Write it
`[M_-, σ(g_1..g_n), M_+]`.

Identify the ray `{k} x N` with `N` by `(k,i) <-> i`. For a finite `M`, let `m_k = |M ∩ {k} x N|`. The increasing
enumeration `beta_{k,M} : N -> Q(k,M)` satisfies `beta_{k,M}(j) = (k, j + m_k)` for large `j`, so it is near
equal to `s̄^(m_k)`.

**Ray germs.** Take an element `h = [M_-, σ(g_1..g_n), M_+]`, with `a_k = |M_+ ∩ ray k|` and
`b_k = |M_- ∩ ray k|`. Off the finite set `M_+`, `h` maps ray `k` into ray `k` as `beta_{k,M_-} g_k beta_{k,M_+}^-1`.
Its germ on ray `k` is therefore `x_k = s̄^(b_k) ḡ_k s̄^(-a_k)`, which lies in `Ĝ` with `eta(x_k) = b_k - a_k`.
Since `Σ a_k = |M_+| = |M_-| = Σ b_k`, the tuple `(x_k)` lies in `Q_n(Ĝ)`. So `germ : H_n(G) -> Q_n(Ĝ)` is a
homomorphism.

**Kernel.** Every element of `H_n(G)` preserves each ray up to finitely many points. So an element with trivial
germ on every ray agrees with the identity off a finite set, i.e. it lies in `FSym([n] x N)`. Conversely,
`FSym([n] x N) <= H_n(G)`: it is the Houghton subgroup's finitary part, as quoted in the proof of Proposition 5.5.
So the kernel is exactly `FSym([n] x N)`.

**Onto.** Let `(x_k) = (s̄^(c_k) ḡ_k)` with `Σ c_k = 0`.
- Put `a_k = max(0, -c_k)` and `b_k = max(0, c_k)`. Then `b_k - a_k = c_k` and `Σ a_k = Σ b_k`.
- Choose finite sets `M_+` and `M_-` with `a_k` and `b_k` points on ray `k`, and any bijection
  `σ : M_+ -> M_-`.
- Choose `g'_k ∈ G` representing `psi_infinity^(a_k)(ḡ_k) = s̄^(-a_k) ḡ_k s̄^(a_k)`, which lies in `Germs(G)` by
  Step 1.
- Then `[M_-, σ(g'_1..g'_n), M_+]` has ray germs `s̄^(b_k) s̄^(-a_k) ḡ_k s̄^(a_k) s̄^(-a_k) = s̄^(c_k) ḡ_k = x_k`.

This proves item 1.

## Step 3. Item 2

**(<=), n >= 3.** `Q_n(Ĝ) = ker ψ` with `ψ = Σ_k eta∘pr_k : Ĝ^n -> Z`. The map `ψ` is onto `Z`, so it is
discrete. If `Ĝ` is finitely presented, then `Ĝ^n` is too, and `±ψ` is nonzero on each of the `n >= 3`
factors. By (I2) with `m = 2`, `[±ψ] ∈ Σ^2(Ĝ^n)`. By (I1) with `n = 2`, `ker ψ` has type `F_2`, i.e. it is
finitely presented.

**(=>), n >= 2.** The map `i(x) = (x, s̄^(-eta(x)), 1, ..., 1)` is a homomorphism `Ĝ -> Q_n(Ĝ)`, because powers of
`s̄` commute. The first projection is a left inverse. By (I3), `Ĝ` is finitely presented if `Q_n(Ĝ)` is.

## Step 4. Item 3, the envelopes E_nu(P)

`E_nu(P)` is strongly shift-similar by Mallery--Zaremsky Proposition 3.27, imported in
`half-finite-generators-with-e2-are-strongly-shift-similar`. Write `N = evens ⊔ odds`, and identify each part
with `N` by `2k <-> k` and `2k+1 <-> k`.

By `mz-envelope-germ-group-is-an-antitwisted-fiber-product`, `Q := Germs(E_nu(P))` contains with index 2 the
group `F^- = {(a,b) in R x R : eta(a) + eta(b) = 0}`. That group is generated by `(lambda_g, 1)`,
`(1, lambda_g)` and `(s, s^-1)`. The flip `ω = (0 1)(2 3)...` is in `E_2`, and its class `ω̄ ∈ Q` swaps the
two parts.

**Two coordinate shifts.** Composing right to left, with `σ(k) = k+1` on each part:
- `s̄ ω̄` sends `2k -> 2k+1 -> 2k+2` and `2k+1 -> 2k -> 2k+1`, so `s̄ ω̄ = (σ, 1)`;
- `ω̄ s̄` sends `2k -> 2k+1 -> 2k` and `2k+1 -> 2k+2 -> 2k+3`, so `ω̄ s̄ = (1, σ)`.

Here `σ` is the generator `s` of `R = R_nu`.

**The index-two subgroup.** Every generator of `Ĝ = <F^-, ω̄, s̄>` preserves or swaps the two parts up to finite
sets. So parity is a homomorphism `Ĝ -> C_2`, and `ω̄` and `s̄` are odd. Its kernel `Ĝ^0` has Schreier
generators, for the transversal `{1, ω̄}`:
- `F^-` and `ω̄ F^- ω̄` (coordinates swapped);
- `s̄ ω̄ = (σ, 1)` and `ω̄ s̄ = (1, σ)`.

All of these lie in `R x R`. Conversely `R x R` is generated by `(lambda_g, 1)`, `(1, lambda_g)`, `(σ, 1)` and
`(1, σ)`, all of which lie in `Ĝ^0`. So `Ĝ^0 = R x R` and `Ĝ = (R x R) ⋊ <ω̄>`.

**Near index.** The near index on `N` of a pair `(a, b)` is `eta(a) + eta(b)`. So `Q_n(Ĝ) ∩ (R x R)^n` has index
`2^n` in `Q_n(Ĝ)`: it is the kernel of the onto parity map `Q_n(Ĝ) -> C_2^n`, which is onto because `ω̄` has
index 0. That subgroup is `ker(Σ_{j=1}^{2n} eta∘pr_j)` on `R^{2n}`.

**Conclusion for n >= 2.** Here `2n >= 4 >= 3`.
- If `R` is finitely presented, Step 3 (<=), with `R` in place of `Ĝ` and `2n` factors, shows this kernel is
  finitely presented. So is `Q_n(Ĝ)`, which contains it with finite index.
- Conversely, if `Q_n(Ĝ)` is finitely presented then so is its finite-index subgroup. That subgroup retracts onto
  `R` by `a -> (a, s^(-eta(a)), 1, ..., 1)`, so `R` is finitely presented by (I3).

## Step 5. Items 4 and 5

**Item 4.** `FSym([n] x N)` is the normal closure of one transposition in `H_n(G)`. So if `H_n(G)` is finitely
presented, so is its germ group. Then item 3 gives the claim for `n >= 2`. For `n = 1`, `H_1 = E_nu(P)` and
`mz-envelope-germ-group-is-an-antitwisted-fiber-product` item 4 gives it.

**Item 5.** `regular-enumerations-can-make-near-shift-free-product` gives `R_nu ≅ P * <s>`. That node has no status line on main. Its route `regular-free-shift-fresh-trajectory-proof` is an elementary back-and-forth construction, which this lane read and found complete. This group is finitely
presented when `P` is. Apply item 3. ∎

**Checks.** At `n = 1` Step 3 has only one factor, and the index-2 subgroup of `Q_1` is `ker(eta + eta)` on
`R x R`. That recovers the two-sided gate, so there is no contradiction with the established MZ gate. The
Stallings–Bieri group `ker(F_2^3 -> Z)` is the case `R = F_2`, `k = 3` of Step 3, and it is finitely presented
(`stallings-bieri-sb3-is-finitely-presented-not-f3`), as the step predicts.
