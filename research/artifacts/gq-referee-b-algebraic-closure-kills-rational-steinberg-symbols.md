# Referee report (gq-referee-b, citation lens): the algebraic closure kills rational Steinberg symbols

**Reviewed.** `algebraic-closure-kills-rational-steinberg-symbols` and its `-proof` (lane gq-infinite-primes,
05a4c7c2e), read on origin/main.

**Verdict: PASS.** Each of the four inputs is correct as used. I pinned each one to a page read at source,
in two primary texts:
- the Dennis–Stein survey, *The functor K_2: a survey of computations and problems*, LNM 342 (1973), local PDF
  `gq/src/k2/ds-survey.pdf`, where PDF page `k` is book page `240 + k`;
- van der Kallen, *Injective stability for K_2*, LNM 551, local PDF `gq/src/k2/vdk.pdf`.

The only unconfirmed item is the theorem number "11.6" in Milnor's book; Dennis–Stein give the page instead.

## (T) Tate: K_2(Q) is torsion

- **Dennis–Stein §11(iii), p. 253**, verbatim: "K_2(Q) = {±1} ⊕ ∐_p (Z/pZ)* [69, p. 101]."
- [69] is, per p. 274, "J. Milnor, Introduction to Algebraic K-theory, Annals of Math. Studies No. 72, Princeton
  University Press, Princeton, 1971".
- The factor at `p = 2` is trivial, so this is the node's `Z/2 ⊕ ⊕_(p odd) (Z/p)^x`. **Match.**
- **Pin:** Milnor, p. 101, via Dennis–Stein §11(iii). I did not see the theorem number 11.6 at source; cite the page,
  or mark 11.6 unverified.

## (S) K_2 of an algebraically closed field is torsion-free

- **Dennis–Stein §11(ii), p. 253**, verbatim: "If X^m − a splits into linear factors for all a ∈ F, then K_2(F) is
  uniquely divisible by m. Hence K_2 of an algebraically closed field is a torsion free divisible group [...]
  [5, (1.2)]."
- [5] is, per p. 267, "H. Bass and J. Tate, The Milnor ring of a global field, these Proceedings" (LNM 342).
- So (S) for `Q̄` is classical (Bass–Tate 1973, (1.2)), and Suslin 1983 is not needed.
- **Pin:** Bass–Tate (1.2), via Dennis–Stein §11(ii). Replace the unpinned Weibel reference.
- The alternative route through Suslin 1987 (`K_2(F)[n] = {ζ_n, F^x}`) is argued correctly, since
  `{ζ_n, γ^n} = {ζ_n^n, γ} = 0`, but it is not read at source.

## (IS) Injective stability for fields, N ≥ 3

- **vdK Theorem 1, §1.1, p. 77**, read at source (report 7a9be50ac): "Let R be a commutative ring with noetherian
  maximal spectrum of dimension d, d < ∞. Let n ≥ d + 2. Then [...] the natural map K_2(n + 1,R) → K_2(R) is an
  isomorphism."
- For a field, `d = 0`. So `K_2(N, F) → K_2(F)` is an isomorphism for `N = n+1 ≥ 3`. **Match.**
- **Wording.** The route says "in the range `N ≥ sr + 2`, with `sr(F) = 1`". Theorem 1 is stated with the
  dimension `d` of the maximal spectrum, not with stable rank. For fields the range is the same, `N ≥ 3`. Restate it
  as "Theorem 1 with `d = 0`".
- **A second source read at source.** Dennis–Stein §12, pp. 253–254: "If A is a discrete valuation ring or a
  homomorphic image thereof, then K_2(A) and K_2(n,A) for n ≥ 3 are presented by the generators {u,v}, u,v ∈ A*,
  subject to the relations (S1) - (S7) [27, Theorems 2.3, 2.5]."
  - A field is such an image, for example `F[[t]] → F`.
  - For Matsumoto, §11 p. 252 cites "[67] (cf. [69, §§11,12])".

## Bimultiplicativity of symbols (item 4)

- **Dennis–Stein §9(a), p. 249**, verbatim:
  > "If u and v commute then {u,v}_α ∈ K_2(n,R) and lies in the center of St(n,R) for any n. [...] If R is a
  > commutative ring and n ≥ 3, these symbols satisfy the identities listed below. (S1) {uv,w} = {u,w} {v,w},
  > {u,vw} = {u,v} {u,w} [...] Proofs of (S1) - (S4) can be found in [69, p. 74]."
- **Pin:** Milnor p. 74, via Dennis–Stein §9(a) (S1). This replaces "Milnor §8–9".
- **It is applied in range.** `C = ⟨ν^(±1), x^(±1)⟩` is commutative because `ν` is central, and the identity holds for
  every `n ≥ 3`, hence stably.
- **Item 1's use.** The same sentence ("{u,v}_α ∈ K_2(n,R)" for commuting `u, v`) is what item 1 needs to put
  `{λ, μ}_N` in `K_2(N, Q)`.

## Argument (checked)

- **Item 1.** Functoriality of `St_N` and `K_2(N, ·)`, plus (IS) for `F`. Here `F → R` extends `Q → R`, and no
  hypothesis on `R` is used.
- **Item 2.** A map from a torsion group to a torsion-free group is zero.
- **Item 4.** `{λ, x} = m{ν, x} ∈ mA` for every `m`. In a finitely generated abelian group `∩ mA = 0`.
- **Item 3.** It rests on the internal nodes `leavitt-resolvent-ring-is-fp-simple-of-char-zero` and
  `field-envelopes-pass-to-algebraic-closures`, which are outside this citation check.
  - The one fact that matters, that the embedding of `Q̄` restricts to the given `Q → R_L`, holds because the
    embedding is `Q`-linear and unital.
