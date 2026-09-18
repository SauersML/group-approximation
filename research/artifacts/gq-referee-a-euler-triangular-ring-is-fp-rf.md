# Referee report (gq-referee-a, proof-gap lens): the triangular Euler ring is finitely presented and residually finite

**Reviewed:** `euler-triangular-ring-is-fp-rf` and its route `-proof` (lane gq-infinite-primes, 8e1c23ab3), read on
origin/main.

**Verdict: PASS.** Items 1–4 hold, and I found no gap. There are two nits. N1 makes explicit a faithfulness fact that
item 4 uses.

## Item 1: the presentation and the Peirce decomposition (the author asked about this)
- *`(1−e)R' = Z(1−e)`.*
  - `R'` is additively spanned by words in the generators, including the empty word 1.
  - Every generator `g` has `g = eg`: by `g = ege` for the four `D`-generators, and by `em = m` for `m`. So
    `(1−e)w = 0` for every nonempty word `w`, while `(1−e)·1 = 1−e`. ✓
- *Words through `m`.* `me = 0` gives `m = m(1−e)`, so `mg = m(1−e)g = 0` for every generator `g`. The surviving
  words are words `w` in `e` and the `D`-generators, the words `wm`, and 1. ✓
- *The four Peirce corners.*
  - `eR'e`: the `D`-words are unchanged, since `w = ewe`, and `e(wm)e = wme = 0`. So `eR'e = D'`.
  - `eR'(1−e)`: `e w (1−e) = w − we = 0`, `e(wm)(1−e) = wm` and `e·1·(1−e) = 0`. So `eR'(1−e) = D'm`.
  - The remaining corners are `(1−e)R'e = 0` and `(1−e)R'(1−e) = Z(1−e)`. ✓
- *The relations match those of `D`.* The four `D`-relations with unit `e` are the first relations of
  `resolvent-presentation-ring-is-residually-finite`: `xx' = x'x = 1`, `xu = (u+l)x` and
  `B(u+1) = (u+1)B = 1`. By Step 1 of `resolvent-ring-has-path-normal-form-proof`, that ring is `D`. So there is a
  unital map `D → eR'e` onto `D'`.
- *The comparison map respects the relations.*
  - `e m = E_11 · [[0,v_0],[0,0]] = [[0,v_0],[0,0]] = m`, and `m e = 0`.
  - `u m = [[0, u v_0],[0,0]] = 0`, since `v_0` is the class of 1 in `D/Du`.
  - The `D`-relations hold in the corner. ✓
- *Injectivity, piece by piece.* The map `R' → T_l` respects the three Peirce pieces, so injectivity can be checked
  on each one.
  - `D → D' → D` and `D/Du → D'm → M` are the identity on generators. The second exists because `um = 0`.
  - `Z → Z(1−e) → Z` is the identity. ✓
- *Generation.* `x^k B x^(−k) = (u+1+kl)^(−1)`, so `u, x, x', B` generate `D`, and `D v_0 = M`.

## Item 2: residual finiteness
- *`M_(r,N)` is a `D`-module.*
  - `lj mod l^r` depends only on `j mod l^(r−1)`, which divides `N`, and `1 + lj` is a unit mod `l^r`.
  - `xu f_j = lj f_(j−1) = (u+l)x f_j`. ✓
- *The fold `M → M_(r,N)` is `D`-linear.*
  - `a ∈ A` acts on `f_j = x^(−j)v_0` by the scalar `a(lj)`, because `u x^(−j) = x^(−j)(u + jl)`.
  - `x` preserves these scalars: `σ(a)` evaluated at `l(j−1)` equals `a(lj)`.
  - So `D` acts `Z_(l)`-linearly on `M`, and it suffices to check the generators. ✓
- *The ring maps.* The product rule `[[dd', dn' + nk'],[0, kk']]` is preserved, and the maps are unital, which item 3
  of the Steinberg node needs. ✓
- *Separation.*
  - The case `d ≠ 0` is exactly "Case δ ≠ 0" of `resolvent-presentation-ring-is-residually-finite-proof` with
    `E = 0`, `d = 1`, `g = 1`. That module is `M_(r,N)`. ✓
  - The cases `k ≠ 0` and `n ≠ 0` are immediate.

## Items 3 and 4
- *The unit group.* `T_l^× = {[[d,n],[0,±1]] : d ∈ D^×}`, and `[[h,n],[0,1]]` has inverse `[[h^(−1), −h^(−1)n],[0,1]]`.
  These units multiply as `(n,h)(n',h') = (n + hn', hh')`. ✓
- *`⟨x, 1+u⟩ ⊂ D^×` is `Z≀Z` (the author asked about this).* This needs `D^× → Aut(M)` to be injective on
  `⟨x, 1+u⟩` (N1).
  - It holds: `d = Σ x^a a_a` acts by `f_j ↦ Σ_a a_a(lj) f_(j−a)`.
  - A nonzero rational function vanishes at only finitely many `lj`, so `D` acts faithfully on `M`.
  - Hence `⟨x, 1+u⟩` maps isomorphically onto `H = ⟨x, β⟩ ≤ Aut(M)`, with `1 + u ↦ β`, and the affine matrices give
    exactly `M ⋊ H = G_l`. ✓

## Nits
- **N1 (items 3 and 4).** "`⟨x, 1+u⟩ ≅ Z≀Z` in its faithful action on `M`" needs faithfulness of `D` on `M`. `H` is
  faithful on `M` by definition, but the identification of the subgroup of `D^×` with `H` is exactly this fact. Cite
  the δ ≠ 0 case of item 2, which implies it because the fold is a `D`-linear surjection, or give the
  rational-function line above.
- **N2 (the first `distinct_from` entry).** It is accurate. Also verified: every corner of `T_l` is `0`, `D`, `Z` or
  `T_l` up to conjugacy, since `D` is a domain and its idempotents are 0 and 1. None contains `Z_(l)`: `A ∩ Q = Z` by
  Gauss's lemma, and there is no unital map `Z_(l) → Z`.
