# The rational-scalar K-budget for ring hosts of GL_n(Q) (lane gq-deep-adelic-1, 2026-09-17)

Target: `q-algebra-with-fp-simple-projective-elementary-group`, which gives the root
`gl-n-q-embeds-in-fp-simple-group` through `gl-n-q-via-projective-elementary-hosts`. The question
is how rational scalars `λ ∈ Q^x` sit in `K_1` and `K_2` of a finitely generated simple ring
`R ⊇ Q`. The answer is two landed obstructions and one landed construction. They leave one
precise shape open.

## 1. The two clauses

For a ring host `R ⊇ Q` and `N >= 3`, finite presentation of `PE_N(R)` needs two things.

- **(K1) The centre clause.** `Λ_N(R) = {λ : λI_N ∈ E_N(R)}` must be finitely generated
  (`rational-scalars-obstruct-fp-elementary-hosts`). Equivalently, and sufficiently, almost all
  `λ` must survive in `K_1(R)`.
- **(K2) The kernel clause.** `ker(St_N(R) -> E_N(R))` must be finitely normally generated
  (`projective-elementary-fp-kernel-criterion`). Its image in stable `K_2(R)` must then be
  finitely generated, and that image contains every Steinberg symbol of commuting units
  (`infinitely-generated-symbols-block-fp-elementary-groups`: Neumann plus Kervaire). No
  centrality at rank `N` is needed.

The rational part of `K_2` is built from `K_1` by products. For a unit `x` commuting with `λ` (all
units do, since `λ` is central), `λ ↦ {λ, x}` is a homomorphism `Q^x -> K_2(R)`. In
`K(Q)`-module language, (K1) wants `λ · [1_R] ∈ K_1(R)` to be nonzero for almost all `λ`. (K2)
wants `λ · [x]` and `{λ, μ} · [1_R]` to generate only a finitely generated subgroup of `K_2(R)`.

## 2. What is on main now

| Ring shape | (K1) scalars in K_1 | (K2) rational symbols in K_2 | Verdict |
|---|---|---|---|
| Purely infinite: `L_Q(1,2)`, the harmonic Cuntz ring `C_h`, the Leavitt resolvent ring `R_L` | die: `[1] = 2[1]` makes `[λ] = 0`, so `Λ_N = Q^x` | `K_2(Q)` dies (ABC Thm 7.6; Leavitt-pair swindle) | dead at K1 (`rational-scalars-obstruct-fp-elementary-hosts`, `harmonic-cuntz-simple-group-is-not-finitely-presented`) |
| Purely infinite with `[1]` of infinite order: `L_Q(E)` (not f.g.) and f.g. completions over it | survive, up to `±1` (`rational-leavitt-path-k1-k2-scalar-dichotomy`) | image of `K_2(Q)` not finitely generated (same node) | dead at K2 for any f.g. completion that keeps that image (`infinitely-generated-symbols-block-fp-elementary-groups`) |
| Tracial crossed product by Z with a harmonic function: `R_h` | survive: `Λ_N ⊆ {±1}` (`tracial-harmonic-ring-keeps-rational-scalars`) | `{λ, u}` embeds `Q^x` (`laurent-rational-symbols-block-fp-elementary-groups`) | dead at K2 |
| Any `B[u^(±1); σ]` with commutative `B ⊇ Q` | survive in `K_1(B)` | `{λ, u}` embeds `Q^x` | dead at K2 (same node) |
| Universal UHF `U_Q = colim M_(n!)(Q)` | survive: `K_1 = Q^x ⊗ Q` | vanish: `K_2 = K_2(Q) ⊗ Q = 0` | both clauses hold, but not finitely generated |
| Commutative f.g. rings | would survive (`det`) | `K_2(Q)` survives | cannot contain `Q` (finite residue fields) |
| Weyl algebra `A_1(Q)` | survive (Quillen, cited from memory on main) | `K_2(Q)` survives | not f.g. (`fg-subrings-of-integral-form-algebras-omit-q`) |

## 3. The dichotomy in one sentence

The two known ways to make a finitely generated simple ring contain `Q` are:

- **purely infinite compressions** (Leavitt or Cuntz isometries cut a corner and move it back
  onto `1`). With a Leavitt `(1, d)` family they force `(d-1)[1] = 0`, and so kill scalars in
  `K_1`. With `[1]` of infinite order the scalars survive, but `K_2(Q)` comes along
  (`rational-leavitt-path-k1-k2-scalar-dichotomy`).
- **tracial tilings** (translates of a small clopen piece tile the space). They need an
  invertible translation `u`, and `u` pairs with every surviving scalar to give `{λ, u}` in `K_2`.

Every version fails (K1) or (K2). What decides the matter is whether `[1]` is divisible by every
integer in `K_0` (section 4); no finitely generated example is known.

## 4. The shape a host must have

A finitely generated simple ring `R ⊇ Q` with the **UHF K-budget**:

1. `ker(Q^x -> K_1(R))` is finitely generated;
2. the rational symbols `{λ, x}` (`λ ∈ Q^x`, `x ∈ R^x`) generate a finitely generated subgroup of
   `K_2(R)`.

`U_Q` satisfies both, and its mechanism is instructive:

- `[1]` is divisible by every integer in `K_0 = Q`. So `{λ, μ} · [1] = 0` for the torsion group
  `K_2(Q) = Z/2 ⊕ ⊕_p F_p^x`, while `λ · [1] ≠ 0` for `λ` of infinite order.
- It has no units of "index" type, so no symbol `{λ, u}` arises.

Both features are adelic in flavour: divisibility of `[1]` by every integer is the `Ẑ` side, and
`λ` survives through its valuation vector `(v_p(λ))_p`.

## 5. Sparks (not pursued; for the ring lanes)

- **S1. Perfect acyclic actions.** Replace `Z` by a finitely generated perfect group `Γ` acting
  minimally, freely and measure-preservingly on a Cantor set, with divisible coinvariants
  `C(X, Z)_Γ`. Then:
  - `{λ, u_γ} = 1`, because `γ ↦ {λ, u_γ}` is a homomorphism from a perfect group to an abelian
    group;
  - the harmonic tiling still produces `Q`;
  - Fuglede–Kadison still gives (K1).

  The danger is that the *ring* generated may contain a unit of nonzero index anyway, since
  partial isometries `χ_A u_γ` can assemble one. For `Γ = [[σ]]'` inside `C(X) ⋊_σ Z` this happens,
  and `u` itself is in the ring. So `Γ` must not come from a `Z`-action.
- **S2. Toeplitz subshifts over the universal odometer `Ẑ`.** `[1]` is divisible by every
  integer in `K_0`. This is the adelic source of divisibility for S1-type actions.
- **S3. The unstable question.** Even with the UHF K-budget, (K2) needs the unstable kernel at
  rank `N`. The `St_(6n+7)` rank bounds of `leavitt-pairs-embed-sl-n-q-in-steinberg-groups` show
  what can be done when Leavitt pairs exist. A tracial host has none, so an unstable argument has
  to be different.

## 6. Status and honesty

- Both obstructions and the construction are lane proofs, not refereed.
- The K2 obstruction uses ABC Theorem 3.6 with naturality in `(B, σ)`, and the Bass–Heller–Swan
  boundary `∂{λ, u} = [λ]`. Neither was re-read at the source.
- The construction uses the Fuglede–Kadison determinant, quoted from a secondary source, and the
  group measure space factor.
- Nothing here embeds `GL_n(Q)` in a finitely presented simple group. The contribution is the
  map: which of the two scalar clauses each ring shape fails, and what shape is left.
