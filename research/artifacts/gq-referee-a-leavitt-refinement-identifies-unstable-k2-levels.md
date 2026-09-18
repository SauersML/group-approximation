# Referee report (gq-referee-a, proof-gap lens): Leavitt refinement identifies the unstable K_2 levels

**Reviewed:** `leavitt-refinement-identifies-unstable-k2-levels` and its `-proof` (lane gq-infinite-primes, 414f75d29),
items 2–4, read on origin/main. Item 1, the Voronetsky/Khanh refinement isomorphism, is a citation and is with
gq-referee-b.

**Verdict: PASS** for items 2–4, given item 1 and Khanh's padded-centrality lemma, both cited. There are two nits.

## Item 2: the block identity and `ι_(r+1)D_r = ι_r` (the author asked about this)
- *`V'` is invertible.* Using `e*e = f*f = 1`, `e*f = f*e = 0` and `ee* + ff* = 1`, the claimed inverse
  `(p,q,w) ↦ (ep+fq, e*w, f*w)` is two-sided:
  - `V'` after the inverse gives `(e*(ep+fq), f*(ep+fq), ee*w + ff*w) = (p,q,w)`;
  - the inverse after `V'` gives `(ee*x + ff*x, e*(ey+fz), f*(ey+fz)) = (x,y,z)`. ✓
- *The block identity.* As a map `R^r ⊕ R^2 → R^(r+1) ⊕ R`, `V = T_r ⊕ u`, with `u(y,z) = ey + fz` invertible (N1).
  So `V(A ⊕ 1 ⊕ 1)V^(−1) = T_rAT_r^(−1) ⊕ uu^(−1) = α_r(A) ⊕ 1`, since `T_r^(−1) = U_r`. ✓
- *Stable compatibility.* `stab∘D_r` and `c_V∘stab` both lift `stab∘α_r∘φ_r` to `E(R)`.
  - Their quotient takes values in the central `K_2(R)`, so it is a homomorphism: if `f g^(−1)` has central values,
    then `f g^(−1)(xy) = f(x) δ(y) g(x)^(−1) = δ(x)δ(y)`. It is trivial, because `St_r(R)` is perfect for `r ≥ 3`.
  - `GL(R)` acts trivially on `K_2(R)` (Milnor), so `ι_(r+1)D_r = ι_r` on `K_2(r,R)`.
  - With item 1, `D_r` maps `U_r` onto `U_(r+1)`. ✓

## Item 3: computability of `D_r^(−1)` (the author asked about this)
- `D_r` is computable on generators by explicit ring words (`ae`, `af`, `e*a`, `f*a`).
- `D_r^(−1)`: given `y`, search for a word `x` and a derivation of `D_r x = y` in `St_(r+1)(R_L)`.
  - Derivations are recursively enumerable, because `St_(r+1)(R_L)` has a recursively enumerable presentation (my
    8ffbfb9b4).
  - The search halts because `D_r` is onto.
  - The output word is not unique, but its element is.
- So the word problem, and recursive enumerability of nontriviality in `U_r`, transfer in both directions. ✓

## Item 4: padded centrality and the kernel identity (the author asked about this)
- *The two maps lift the same map.* `j(D_r x)` and `ω_0 jj(x) ω_0^(−1)` both lift `α_r(φ_r x) ⊕ 1`, by item 2's
  block identity. So `c(x) ∈ K_2(r+2,R)`.
  - `c` itself need not be a homomorphism, since `K_2(r+2)` need not be central. The proof handles this correctly by
    padding first.
- *Padding.* `j(c(x)) ∈ j(K_2(r+2))` is central in `St_(r+3)` by padded centrality. So `x ↦ j(c(x))` is a homomorphism
  into a central subgroup, by the same identity, and it is trivial by perfectness. This gives
  `j j D_r(x) = ω jjj(x) ω^(−1)` with `ω = j(ω_0)`. ✓
- *The kernel identity.* For `b ≥ 2`, `j^b(D_m x) = j^(b−2)(ω) j^(b+1)(x) j^(b−2)(ω)^(−1)`. So `j^b(D_m x) = 1` exactly
  when `j^(b+1)(x) = 1`.
  - `D_m : K_2(m) → K_2(m+1)` is bijective, so `ker(j^(b+1)|K_2(m)) = D_m^(−1)(ker(j^b|K_2(m+1)))`. ✓
  - Iterating gives `ker(j^b|K_2(m)) ≅ ker(j^2|K_2(m+b−2))`.
  - `U_m = ∪_b ker(j^b|K_2(m))`, by the directed colimit `St(R) = colim St_k(R)`.
- *The equivalence.* "`U_3 = 1` iff `j^2` is injective on every `K_2(m)`" follows with item 3.
  - (⇒) `ker(j^2|K_2(m)) ⊆ U_m ≅ U_3`.
  - (⇐) By the isomorphisms, every `ker(j^b|K_2(m))` is trivial. ✓
- *Hypothesis bookkeeping.* The kernel identity at every `m` needs `V_m ∈ E_(m+2)` for every `m`. That follows from
  `V' ∈ E_3(R)` by block embedding (N2).
  - `V'` has entries in `L_Q(1,2) ⊆ R_L`. So `GL_3(L_Q(1,2)) = E_3(L_Q(1,2))` would suffice, as stated.

## Nits
- **N1 (item 2).** Write `V = T_r ⊕ u`, with `u = (e f) : R^2 → R` and `u^(−1) = (e*; f*)`. The block identity is then
  one line.
- **N2 (item 4).** State the hypothesis as "`V' ∈ E_3(R)`". It gives `V_r ∈ E_(r+2)(R)` for all `r` at once, which the
  kernel identity at every level uses.
