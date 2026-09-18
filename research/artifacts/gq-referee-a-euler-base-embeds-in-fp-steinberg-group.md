# Referee report (gq-referee-a, proof-gap lens): the Euler base embeds in a finitely presented Steinberg group

**Reviewed:** `euler-base-embeds-in-fp-steinberg-group` and its route `-proof` (lane gq-infinite-primes, 8e1c23ab3),
read on origin/main.

**Verdict: FAIL at one step, repairable. The repair is given below and is verified.**
- Items 1 and 2 PASS: `St_N(T_l)` is finitely presented for `N ≥ 5` and contains `M ⊇ Z_(l)`.
- In item 3, finite generation and residual finiteness of `E_N(T_l)` PASS.
- **The failing step** is item 3, "Contains `G_l`":
  - the map `g ↦ diag(g, g^(−1), 1, …, 1)` is not a homomorphism, because `G_l` is not abelian;
  - the statement survives with a different map (R below), so the node stays ESTABLISHED once the map is replaced.

## Items 1 and 2 (PASS)
- `T_l` is a finitely presented unital ring by item 1 of `euler-triangular-ring-is-fp-rf` (PASS in the companion
  report).
- `steinberg-groups-of-fp-rings-are-fp-in-rank-five` covers noncommutative rings `Z⟨g_1..g_d | ρ_t⟩` with `n ≥ 5`.
- `x_12(a)x_12(b) = x_12(a+b)`. The image in `E_N(T_l)` has `(1,2)` entry `ι(n)`, which is injective. ✓

## Item 3
- *Finitely generated (PASS).*
  - The set of `r` with every `e_ij(r)` in the subgroup contains 1 and the six generators, and is closed under `±`.
  - It is closed under products via `[e_ij(a), e_jk(b)] = e_ik(ab)` with `i, j, k` distinct, since `N ≥ 3`.
  - So it is all of `T_l`. ✓
- *Residually finite (PASS).* The separating ring maps of the companion node are unital. So they induce
  `GL_N(T_l) → GL_N(finite)`, and an entry of `g − I` survives. ✓
- *Whitehead's formula (PASS).* It holds over noncommutative rings:
  - `e_12(a)e_21(−a^(−1))e_12(a) = [[0, a],[−a^(−1), 0]]`;
  - multiplying by the same matrix at `a = −1`, which is `[[0,−1],[1,0]]`, gives `diag(a, a^(−1))`.
- **The failing step.** `diag(g, g^(−1)) diag(h, h^(−1)) = diag(gh, g^(−1)h^(−1))`, while the image of `gh` is
  `diag(gh, h^(−1)g^(−1))`. These agree only if `gh = hg`.
  - In `G_l`, `x(1+u)x^(−1) = 1+u+l ≠ 1+u`.
  - So `g ↦ diag(g, g^(−1), 1, …, 1)` is not a homomorphism on `G_l`. Its second slot is an anti-homomorphism.

## R: the repair (verified)
- **The twist `c`.** Let `c : H = ⟨x, 1+u⟩ → D^×` be given by `c(x) = x^(−1)` and `c(1+u) = B = (1+u)^(−1)`.
  - `H ≅ Z≀Z = ⟨x, β | [β, x^k β x^(−k)] (k ≥ 1)⟩`, and the images satisfy
    `[B, x^(−k) B x^k] = [B, σ^(−k)(B)] = 1` in the commutative ring `A`. So `c` is a homomorphism.
  - By construction `c(s) = s^(−1)` on the four letters `x^(±1)`, `(1+u)^(±1)`.
- **The embedding.** Let `π : G_l → H` be the quotient, and define
  `Φ(g) = diag(g, c(π(g)), 1, …, 1)`, with units of `D` read as `[[h,0],[0,1]] ∈ T_l^×`.
  - `Φ` is a homomorphism, since both slots are.
  - `Φ` is injective, since its first slot is.
- **It lands in `E_2`.**
  - For `h = s_1 ⋯ s_k` in the letters, `diag(h, c(h)) = Π diag(s_i, s_i^(−1))`, and each factor lies in `E_2` by
    Whitehead.
  - For the `M`-part, write `g = (1 + ι(n))·h`, where `ι(n) = ab` with `a = ι(n)` and `b = 1−e`, and `ba = 0`. The
    identity
    `e_12(a) e_21(b) e_12(−a) e_21(−b) = diag(1+ab, 1)`, valid whenever `ba = 0`, gives
    `diag(1 + ι(n), 1) ∈ E_2(T_l)`.
    - Check: `e_12(a)e_21(b) = [[1+ab, a],[b, 1]]`, then `·e_12(−a)` gives `[[1+ab, −aba],[b, 1−ba]] = [[1+ab,0],[b,1]]`,
      then `·e_21(−b)` gives `diag(1+ab, 1)`.
  - So `Φ(g) = diag(1+ι(n), 1) · diag(h, c(h)) ∈ E_2(T_l) ⊆ E_N(T_l)`. ✓
- **Wording.** Replace "through `g -> diag(g, g^(-1), 1, ..., 1)` (Whitehead)" in the statement and in the proof by
  `Φ`, with the two displayed identities.

## The Reading paragraph
- *The lever.* `[x_ij(d), x_jk(ι(n))] = x_ik(ι(dn))` is the Steinberg relation with `ab = ι(dn)`. ✓
- *Units.* "The only units are `D^×` and `±1`, up to the unipotent `M`-part" is correct:
  `T_l^× = {[[d,n],[0,±1]] : d ∈ D^×}`.
- *Corners.* "`Z_(l)` is not a subring of any corner" is correct; see N2 of the companion report.
- The route to `z-localized-embeds-in-fp-rf-group` is not reviewed here.
