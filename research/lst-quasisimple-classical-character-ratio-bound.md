---
rg: 2
id: lst-quasisimple-classical-character-ratio-bound
kind: claim
title: Larsen–Shalev–Tiep bound character ratios of finite quasi-simple classical groups at noncentral elements by 2^(-1/481)
distinct_from:
  dense-support-character-ratios-of-sl-n-2-vanish: that imports the same theorem only at elements of support proportional to N in SL_N(2), where the ratios tend to zero; this imports it at support at least 1, for every finite quasi-simple classical group, as a uniform gap below 1 at every noncentral element
---

**ESTABLISHED by citation** (`lst-quasisimple-classical-character-ratio-bound-citation`).

Let `Γ` be a finite quasi-simple classical group over `F_q`, and `g ∈ Γ` noncentral. Then

```text
|χ(g)|/χ(1) < q^(-1/481) <= 2^(-1/481)    for every nontrivial irreducible character χ of Γ.        (LST1)
```

So every family of finite quasi-simple classical groups, of any ranks, over any finite fields, is θ-gapped with
`θ = 2^(-1/481)`, in the sense of `fp-simple-groups-have-no-gapped-finite-unitary-models`.

**Derivation from the source.**
- Theorem 1.2.1 of Larsen–Shalev–Tiep gives `|χ(g)|/χ(1) < q^(-√N/481)` when `supp(g) >= N`.
- A noncentral `g` has `supp(g) >= 1`:
  - `supp(g) = 0` means the natural representation `ρ` sends `g` to a scalar.
  - Then `[g,h] ∈ ker ρ` for every `h`, and `ker ρ` is central, so `gZ(Γ)` is central in `Γ/Z(Γ)`.
  - `Γ` is quasi-simple, so `Γ/Z(Γ)` is simple nonabelian, and therefore `g ∈ Z(Γ)`.
- Take `N = 1`.
