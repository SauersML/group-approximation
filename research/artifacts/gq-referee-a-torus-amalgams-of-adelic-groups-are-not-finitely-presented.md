# Referee report (gq-referee-a, proof-gap lens): torus amalgams of adelic groups are not finitely presented

**Reviewed:** `torus-amalgams-of-adelic-groups-are-not-finitely-presented` and its `-proof` (lane gq-infinite-primes,
a74bcb9ce), read on origin/main.

**Verdict: PASS** for items 1–6. There is one required wording fix (W1) in the Setting's list of examples, and two
nits. Cornulier's Theorem 1.1 and Example 3.5, and Cannon–Floyd–Parry, are for the citation lens.

## Checks
- **Step 0.**
  - For `GL_n`, conjugation by `t` with `t_i = 1/b` gives `x_ij(a/b) = t x_ij(a) t^(−1)`, since
    `t x_ij(c) t^(−1) = x_ij(c t_i/t_j)`.
  - For `SL_n`, `t_i = 1/b` and `t_j = b` give `t_i/t_j = b^(−2)`, so `t x_ij(ab) t^(−1) = x_ij(a/b)`, with
    `det t = 1`.
  - For `Aff`, `m_r τ^c m_r^(−1)` is translation by `rc`. ✓
- **Step 1: the compatibility of `L → E_S` on `C(Z)` (the author asked about this).**
  - Take `c ∈ C(Z) = C ∩ Γ(Z)`. Along `Γ(Z) ⊆ Γ_S`, it lies in `C ∩ Γ_S = C_S`. In `G_S = Γ_S *_(C_S) C` it is
    identified with `c ∈ C`, and in `E_S = G_S *_C B` with the image of `c` in `B`. That is also the image along
    `B`. So `L → E_S` is well defined. ✓
  - The maps `G_S → G_(S')` and `G_S → Γ` agree on `C_S` for the same reason.
  - The composite `L → E_S → E_(S')` is `L → E_(S')`, so the kernels increase.
- **Step 1: the colimit.** Directed colimits commute with pushouts, and `B` and `C` are constant over a directed
  index set. So `colim G_S = Γ *_(∪C_S) C = Γ *_C C = Γ`, and `colim E_S = Γ *_C B`. By (DC), `ker φ = ∪_S ker(L → E_S)`.
  ✓
- **Step 2: the normal form.**
  - `d_p^(−1) x_21(c) d_p = x_21(pc)`: with `t = d_p^(−1)`, `t_2/t_1 = p`.
  - `t_p^(−1) x_21(c) t_p = x_21(p^2 c)`, and `m_p τ m_p^(−1) = τ^p`.
  - Alternation: the dilations lie in `C ∖ C_S`, because `p^(±1) ∉ Z[1/S]`. `x_21(1)` and `x_21(−p)` lie in
    `Γ_S ∖ C_S`, because `C ∩ x_21(Q) = 1`, and `τ^(±…)` are not dilations.
  - So `w_p` is reduced of length 4 in `G_S`, and `G_S` embeds in `E_S`. ✓
- **Step 3.** (FP) makes `ker φ` the normal closure of finitely many elements of `L`. Each lies in some
  `ker(L → E_(S_i))`, and these kernels are normal and increasing. So `ker φ ⊆ ker(L → E_S)`, and `w_p` with
  `p ∉ S` contradicts this. ✓
- **Item 3.**
  - `σ_h` applied entrywise is an automorphism of `N_n(Q)`: entries of products of monomial matrices are products of
    single entries, and `σ_h` is multiplicative.
  - `h ↦ σ_h` is a homomorphism for a left action.
  - Finite generation of `N_n(Q) ⋊ H` follows from one representative prime per orbit.
  - `N_n(Q)` contains the diagonal subgroup and meets `x_21(Q)` trivially, so item 1 applies. ✓
- **Item 4: the universal-property step (the author asked about this).**
  - `⟨⟨Γ(Z)⟩⟩_Π = ⟨⟨M⟩⟩_Π`.
  - Maps out of `Π/⟨⟨M⟩⟩` are the pairs `(f, g)` agreeing on `C` with `f(M) = 1`. So `Π/⟨⟨M⟩⟩` is the pushout
    `Γ/M ← C → B`.
  - `C → Γ/M ≅ Q_>0` is onto, since `|det|` of the diagonal is onto. So `f` is determined by `g`, and the pushout is
    `B/⟨⟨C ∩ M⟩⟩_B`.
  - For monomial `c`, `det(h·c) = σ_h(det c)`, because `det c` is a sign times the product of the entries and
    `σ_h(−1) = −1`. So `C ∩ M = ker(|det|)` is `H`-invariant, hence normal in `C ⋊ H`.
  - This gives `(C/C∩M) ⋊ H = Q_>0 ⋊ H = Z ≀_P H`. The case `n = 1`, with `C ∩ M = {±1}`, is the same. ✓
- **Item 4: the Thompson example.**
  - `T` acts faithfully and 2-transitively on the dyadic points of the circle: map one dyadic arc to another by a
    dyadic PL homeomorphism. The stabilizer of 0 is `F`. So `X^2` has two orbits. ✓
- **Item 5.**
  - `σ_(h,n) m σ_(h,n)^(−1) = h·m`, since `(mw)_i = m_(i,π(i)) w_(π(i))` and `σ_h` is multiplicative with `σ_h(0) = 0`.
  - So `(m,h) ↦ m σ_(h,n)` is a homomorphism: `m σ_h m' σ_(h')` equals `m (h·m') σ_(hh')`.
  - It agrees with the inclusion on `N_n(Q)`. ✓
- **Item 6.** Conjugating `(BS_p)` gives `d_q^(−1) v d_q = v^p`. If `v = x_21(t)`, then `x_21(qt) = x_21(pt)`, so
  `t = 0`. ✓
- **The consequences.**
  - The map `φ : K_2^T → T` is well defined because `T` acts faithfully on `P`, so distinct `h` give distinct `σ_h`.
  - `⟨e, σ_T⟩ ≅ Z ≀_P T`, and `diag(a,1)^(−1) u(1) diag(a,1) = u(1/a)`. ✓

## Required wording fix
- **W1 (the examples in the Setting).** "Any upper parabolic" is false as stated.
  - An upper parabolic whose first diagonal block has size at least 2 contains `x_21(Q)`. Examples are `GL_n` itself,
    and for `n = 3` the parabolic of type `(2,1)`.
  - For `C = Γ` the amalgam is `B`, which can be finitely presented.
  - The hypothesis actually used is that `C` meets `x_21(Q)` trivially. So the examples should read "any upper
    parabolic whose first block has size 1, for instance the Borel subgroup or the parabolic of type `(1, n−1)`".

## Nits
- **N1 (Step 1).** Spell out the compatibility on `C(Z)` in one line, as above. The route now says only that "all
  these maps commute".
- **N2 (item 3).** Record that `h ↦ σ_h` is a homomorphism because the action on `P` is a left action. That is what
  makes `N_n(Q) ⋊ H` and the map of item 5 well defined.
