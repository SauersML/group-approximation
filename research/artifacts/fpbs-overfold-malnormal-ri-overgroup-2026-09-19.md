# One-generator relative inertia over malnormal rank-2 hosts: reduction and certificate obstructions

swarm-0917-w19-w19-fp-follow, host-geometry follow-through, 2026-09-19.
Target: [[fpbs-mal-overfold-merges-never-help]] (O). Scripts and outputs are in
`experiments/fpbs-overfold-malnormal-ri-2026-09-17/`. Status of the target:
still OPEN. This note gives no proof of (O) and no counterexample. It proves
four structural facts. Together they explain why every hunt so far (≈170k
homological trials in w17/w18, and the runs below) has found nothing, and they
reduce the k = 1 case of relative inertia to one clean statement E(r).

## Setting

`F = F(a,b)`, `φ(a) = a`, `φ(b) = b a b^-2`, `L_j = φ^j(F)`, so
`L_1 = ⟨a, t⟩` with `t = b a b^-2`. All `L_j` are malnormal, of rank 2. For
f.g. `X ≤ J`, `rk(J : X)` is the least `k` with `J = ⟨X, g_1..g_k⟩`.

* **(RI_B)** relative inertia: `rk((J ∩ B) : X) ≤ rk(J : X)` for f.g. `X ≤ B`
  and f.g. `J ⊇ X`. From w17 (Proposition 3 there): (RI_{L_j}) implies (O).
* **Known before this note (w19-fp-last1).** (RI_B) FAILS for the
  non-malnormal `B = ⟨b, a b^2 a^-1⟩`, with `X = ker(B → S3)` and `g = a`.
  Lemma 2: a violation with `J ⊇ B` needs `rk J ≤ rk B`, `J = ⟨B, g⟩`,
  and `J ≠ B`.

## 1. Lemma R (reduction to an equal-rank top case)

**Lemma R.** Let `B ≤ F` be malnormal, `X ≤ B`, `J = ⟨X, g_1..g_k⟩` and
`Y = J ∩ B`.

1. `Y` is malnormal in `J`.
2. The instance `(B, X, J)` of (RI_B) is literally the instance `(Y, X, J)`
   of (RI_Y) in the ambient group `J`, and that instance is a top case
   (`J ⊇ Y`).

*Proof.* Take `x ∈ J ∖ Y`. Then `x ∉ B`, so `Y^x ∩ Y ⊆ B^x ∩ B = 1`. Also
`J ∩ Y = Y = J ∩ B`. ∎

**Corollary R1 (rank-2 hosts, k = 1).** Let `rk B = 2`. The strengthened
Hanna Neumann inequality (Friedman; Mineyev) gives
`rk Y − 1 ≤ (rk J − 1)(rk B − 1) = rk J − 1`, so `rk Y ≤ rk J`. At `k = 1`, a
violation needs `rk(Y : X) ≥ 2`. Then `Y ≠ J`, and Lemma 2, applied in ambient
`J`, forces `rk J ≤ rk Y`. So `rk Y = rk J =: r`.

`Y` also has infinite index in `J`: a proper finite-index subgroup of a free
group of rank `r ≥ 2` has larger rank, and for `r = 1` malnormality gives
`Y = J`. Hence (RI_B) at `k = 1`, for every malnormal rank-2 `B`, follows from
this statement:

> **E(r)**, for all `r ≥ 2`. Let `Y ≤ F_r` be malnormal, of rank `r` and of
> infinite index, and let `X ≤ Y`. If `F_r = ⟨X, g⟩`, then `Y = ⟨X, h⟩` for
> some `h ∈ Y`.

The reduction is exact. E(r) is itself the top case of (RI_Y) at `k = 1`,
with a malnormal host of rank `r`. For `B = L_1`, Section 5 pins the top case
down further (`J = F`).

## 2. Free-orbit structure of `Y` over `X`

Keep the notation of Lemma R with `k = 1`, and put `P = X * ⟨g⟩` (abstract
free product). Let `π : P → J` be the natural surjection, and let
`Ω = Y\J` (right cosets), a transitive `J`-set with base point `ω_0 = Y`.

By malnormality, the stabiliser in `J` of each `ω ≠ ω_0` meets `Y`, and hence
`X`, trivially. So `X` acts freely on `Ω ∖ {ω_0}`.

`H = π^{-1}(Y) ≤ P` is the stabiliser of `ω_0` for the pulled-back action.
Bass–Serre for `P` acting on `Ω` gives `H = X * π_1(Δ)`. Here `Δ` is the
graph whose vertices are the `X`-orbits on `Ω` and whose edges are
`ω → ω g`. Only the base vertex carries a nontrivial vertex group (`X`),
because all the other `X`-orbits are free.

Consequently `Y = π(H) = ⟨X, π(loops of Δ)⟩`. Every new element of `Y` over
`X` is a product along a loop of `Δ` through free orbits: `g^{±1}` moves
alternating with elements of `X`.

The non-malnormal counterexample works by conjugation: a nontrivial
stabiliser at a non-base orbit feeds a second, independent generator. That
mechanism is absent here. This is the structural reason the malnormal case
should behave differently. Turning it into a proof of E(r) is what remains:
one would have to show that such loops can be traded for one generator.

## 3. Proposition N (extendable quotients certify nothing)

**Proposition N.** Let `X ≤ Y ≤ J` with `J = ⟨X, g_1..g_k⟩`. Suppose an onto
`ρ : Y → G` is the restriction of a homomorphism `σ : J → G`. Then
`G = ⟨ρX, σg_1, .., σg_k⟩`. So the finite-quotient bound
`rk(Y : X) ≥ min{m : ⟨ρX, h_1..h_m⟩ = G}` is at most `k`, and `ρ` cannot
certify a violation of relative inertia.

*Proof.* `G = ρY = σY ⊆ σJ = ⟨σX, σg_i⟩ = ⟨ρX, σg_i⟩ ⊆ G`. ∎

The same holds for homology certificates. A lower bound `d(coker(H_1 X → H_1 Y)) ≥ m`
is a finite-quotient bound through a finite abelian quotient of `Y` that
kills `X`. So every certificate of a violation, whether homological or
quotient-based, must be **non-extendable** to `J`.

## 4. Corollary N1 (the top case for `L_j` is nilpotently invisible)

`φ^j : F → L_j` is an isomorphism. The composite `F → L_j ↪ F` is the
endomorphism `φ^j`, and `H_1(φ)` has matrix `[[1,1],[0,−1]]`, with
determinant −1. So `L_j ↪ F` is an `H_1`-isomorphism, and `H_2` vanishes for
free groups. By Stallings' theorem, `L_j/γ_c L_j → F/γ_c F` is an isomorphism
for every `c`.

**Corollary N1.** Every homomorphism from `L_j` to a nilpotent group extends
to `F`, and hence to every `J ⊇ L_j`. By Proposition N, a top-case
(`J ⊇ L_j`) violation of (RI_{L_j}) cannot be certified by:

* `Z`- or `F_p`-homology;
* any p-group quotient;
* any nilpotent quotient.

This explains the zero homological violations in the ≈170k w17/w18 trials. In
the top case they could not have been anything else.

Computation (`extend.py`, `extend.txt`) counts the onto `ρ : L_1 → G` that do
**not** extend to `F`. Restriction is the word map `(A, B) ↦ (A, B A B^-2)`.

| G | onto ρ | non-extendable |
|---|---:|---:|
| C2×C2, D4, Q8, C3×C3, D5 | 6, 24, 24, 48, 60 | 0 |
| S3 | 18 | 6 |
| A4 | 96 | 24 |
| S4 | 216 | 168 |
| A5 | 2280 | 1320 |

The first row is consistent with N1. D5 is not nilpotent, but all its `ρ`
extend as well.

## 5. Proposition O (overgroups of `L_1`)

**Proposition O.** The only subgroups of rank 2 in `F` that contain `L_1` are
`L_1` and `F`.

*Proof.* The core graph `C_1` of `L_1` has vertices `o, v1, v2` and edges
`o -a-> o`, `o -b-> v1`, `v1 -a-> v2` and `v1 -b-> v2`. Let `J ⊇ L_1` have
rank 2. The based morphism from `C_1` to the Stallings graph `Γ_J` has an
image `Z`, a folded subgraph with `π_1 Z ⊇ L_1`. So `rk Z ≥ 2 = rk Γ_J`, and
therefore `Γ_J = Z`, because `Γ_J` is a core graph with the base point in `Z`.

`Z` is `C_1` modulo a fold-closed vertex partition. Every nontrivial partition
of `{o, v1, v2}` folds to the full partition:

* `{o,v1}` gives two `a`-edges out of `o`;
* `{o,v2}` gives two `a`-edges into `o`;
* `{v1,v2}` gives two `b`-edges into `v1`, from `o` and from `v1`.

The trivial partition gives `J = L_1`, and the full partition gives the rose,
so `J = F`. ∎

So a `k = 1` top-case violation of (RI_{L_1}) (Lemma 2: `J = ⟨X,g⟩ ≠ L_1`,
`rk J ≤ 2`) has **`⟨X, g⟩ = F`**.

## 6. φ-monotonicity reformulation

Write `X = φ(X_0)`. Because `φ : F → L_1` is an isomorphism,
`rk(L_1 : X) = rk(F : X_0)`. The `J = F` instances of (RI_{L_1}), with any
`k`, are therefore exactly:

> **(Mon_φ)** `rk(F : X_0) ≤ rk(F : φ(X_0))` for every f.g. `X_0 ≤ F`.

The endomorphism has to be special. For the non-malnormal
`ψ : a ↦ b, b ↦ a b^2 a^-1` (image `⟨b, a b^2 a^-1⟩`), `X_0 = ker(F → S3)`
gives `rk(F : X_0) = 2` but `rk(F : ψ X_0) = 1`. This is the w19
counterexample. So the analogue (Mon_ψ) is false, and any proof of (Mon_φ)
must use a property that `ψ` lacks. Malnormality of the image is the obvious
candidate.

`L_1` is not a retract of `F`. Suppose `r : F → L_1` restricts to the identity
on `L_1`. Then `φ^{-1} ∘ r : F → F` is onto, hence an automorphism (the Hopf
property). So `r` is injective, and `r(r(x)) = r(x)` forces `r(x) = x`, which
gives `F = L_1`. That is false. So (Mon_φ) does not follow from a retraction
argument.

## 7. (G_j) implies (O)

**(G_j).** `rk(M ∩ L_j : M ∩ L_{j+1}) ≤ rk(M : M ∩ L_{j+1})` for f.g. `M ≤ F`.

*(G_j) ⇒ (O) at level `j`.* In relative-rank form, (O) says
`deep = min{k : ⟨K, g_1..g_k⟩ ⊇ K'} ≥ law = rk(K' : K)`, where
`K = S ∩ L_{j+1}`, `K' = S ∩ L_j` and `g_i ∈ S`. Take a minimal witness
`M = ⟨K, g_1..g_deep⟩ ≤ S`, so that `M ⊇ K'`. Then:

* `K ≤ M ∩ L_{j+1} ≤ S ∩ L_{j+1} = K`;
* `K' ≤ M ∩ L_j ≤ S ∩ L_j = K'`.

(G_j) gives `law = rk(K' : K) ≤ rk(M : K) ≤ deep`. ∎

(G_j) is the special case of (RI_{L_j}) with `B = L_j`,
`X = M ∩ L_{j+1}` and `J = M`. So (RI_{L_j}) ⇒ (G_j) ⇒ (O).

The converse (O) ⇒ (G_j) is not clear. Suppose there is a finite-index
`S ⊇ M` with `S ∩ L_{j+1} = M ∩ L_{j+1}` and `S ∩ L_j = M ∩ L_j`. Then (O) at
`S` gives `rk(M ∩ L_j : M ∩ L_{j+1}) ≤ deep ≤ rk(M : M ∩ L_{j+1})`, which is
(G_j).

LERF (completing `Γ_M` to a finite cover `Γ_S`) only gives that `M ∩ L_j` and
`M ∩ L_{j+1}` are free factors of `S ∩ L_j` and `S ∩ L_{j+1}`. The reason is
that `Γ_M ×_R C_j` is a subgraph of `Γ_S ×_R C_j`. The completion edges can
add new loops, so the equalities above can fail.

## 8. Computations

All runs are in `experiments/fpbs-overfold-malnormal-ri-2026-09-17/`.
`stall.py` and `maln.py` are copied unchanged from
`experiments/fpbs-overfold-nonabelian-ri-2026-09-17/` (Stallings folding and a
malnormality test).

`ri1.py` is the `k = 1` (RI_B) hunt with non-normal `X`. The script has four
steps:

1. Draw `X` random (1–3 generators).
2. Draw `g` random with `|g| ≤ 7`.
3. Compute `Y = ⟨X,g⟩ ∩ B` by pullback.
4. Certify `rk(Y:X) ≥ 2` by homology (mod p, p ≤ 47, and over Q), or by an
   onto map to C2², S3, D4, Q8, A4, C3², D5, S4 or A5 with no `h` such that
   `⟨ρX, h⟩ = G`.

`python3 ri1.py selftest` reproduces the w19 counterexample
(`rk X = 7`, `rk J = 2`, `rk Y = 2`, certificate `quotient S3 |ρ(X)| = 1`).

| run | trials | Y ≠ X | J ⊇ B | certified |
|---|---:|---:|---:|---:|
| `L1_1.txt` (B = L_1) | 356 | 17 | 15 | 0 |
| `L2_1.txt` (B = L_2) | 271 | 8 | 8 | 0 |
| `malr2_1.txt` (random malnormal rank 2) | 376 | 7 | 6 | 0 |
| `anyr2_1.txt` (random rank 2) | 380 | 18 | 12 | 0 |
| `G1_1.txt` ((G_1), M = ⟨X_0 ≤ L_2, g⟩) | 600 | 53 | – | 0 |
| `G1_2.txt` ((G_1), seed 2) | 600 | 40 | – | 0 |

In the (G_1) runs, `rk Y` was 2 in 89 cases and 3 in 4 cases.

**Targeted top case.** By Proposition N, only non-extendable `ρ` can certify
anything.

* `nonext.py` samples rank-2 `B`, takes every non-extendable onto `ρ : B → G`
  (one per kernel), and searches all `g` with `|g| ≤ LMAX` for
  `⟨ker ρ, g⟩ ⊇ B`. Each hit is a violation.
  * Sanity check `nonext_nonmal_S3_6.txt` (non-malnormal `B`, S3,
    `|g| ≤ 6`): 60 `B`, 142 non-extendable kernels, **15 hits**. The method
    does find the known phenomenon.
* `longg.py` does the same for `B = L_1`, exhausting every non-extendable
  kernel of an onto `ρ : L_1 → G` over long `g`. The outputs are
  `longg_L1_{S3_12,A4_11,S4_9,A5_8}.txt` and, for random malnormal `B`,
  `nonext_mal_{S3_8,A4_7}.txt`. Final tallies are recorded in Section 9.

**Witness search for the top case of `L_1`** (`witness_h.py`). Draw a random
`X ≤ L_1`. When some `g` gives `⟨X, g⟩ = F` (Proposition O), look for
`h ∈ L_1` with `⟨X, h⟩ = L_1`.

* `witness_h_1.txt`: 107 hits, and `h` was found in all 107. Only 17 of them
  had `g ∉ L_1`.
* `witness_h_2skip.txt` (`g ∈ L_1` skipped, `|g| ≤ 7`, up to 4 generators in
  `X`): **106 nontrivial hits, `h` found in all 106**. Every time, `h` was one
  of the two basis elements: `a` in 59 cases, `t` in 47.

The last pattern suggests a sharper conjecture for the top case of `L_1`:

> **(W)** If `X ≤ L_1` and `⟨X, g⟩ = F` for some `g`, then `⟨X, a⟩ = L_1` or
> `⟨X, t⟩ = L_1`.

(W) implies E(2) for `Y = L_1` at `k = 1`. It is only an observation from 106
cases.

`witness_h_3skip.txt` (seed 3, up to 6 generators in `X`) gives **79 more
nontrivial hits, `h` found in all 79**, again always `a` (48) or `t` (31).
The total for (W) is **185 of 185**.

## 9. Targeted top-case searches: final tallies

Each run below asks for a `g` with `⟨ker ρ, g⟩ ⊇ B` and `g ∉ B`. A hit would
be a `k = 1` violation. By Proposition N and Corollary N1, only non-extendable
`ρ` can give one.

**`B = L_1`, `longg.py`: every non-extendable kernel, all reduced `g` up to
length `LMAX`.**

| G | LMAX | distinct kernels | rk X | `g` tested per kernel | hits |
|---|---:|---:|---:|---:|---:|
| S3 | 12 | 1 | 7 | 1,061,838 | 0 |
| A4 | 11 | 1 | 13 | 353,694 | 0 |
| S4 | 9 | 7 | 25 | 39,156 | 0 |
| A5 | 8 | 11 | 61 | 12,994 | 0 |

These cover every non-extendable onto `ρ : L_1 → G` for these four groups, up
to kernel equality.

**Random `B`, `nonext.py`: non-extendable kernels.**

| run | B | G | LMAX | #B | non-ext. kernels | hits |
|---|---|---|---:|---:|---:|---:|
| `nonext_nonmal_S3_6.txt` | non-malnormal | S3 | 6 | 60 | 142 | **15** |
| `nonext_mal_S3_8.txt` | malnormal | S3 | 8 | 150 | 200 | 0 |
| `nonext_mal_A4_7.txt` | malnormal | A4 | 7 | 80 | 121 | 0 |

The contrast is sharp. The same search finds violations at a rate of about 1 in
10 non-extendable kernels for non-malnormal hosts, and finds none in 321
malnormal kernels, even at a longer `g`. This is the strongest evidence so far
that malnormality is exactly what (RI) needs.

## 10. What is left

* **E(2) for `Y = L_1`** (the `k = 1` top case of (RI_{L_1}), equivalently
  (Mon_φ) at `rk(F : φX_0) = 1`), and the sharper (W). The free-orbit
  structure (Section 2) and the gadget description of `Γ_{φ X_0}` are the
  natural tools. `Γ_{φ X_0}` is `Γ_{X_0}` with each `b`-edge replaced by the
  path `b a b^-1 b^-1`, then folded into the fibres over `o, v1, v2` of `C_1`.
* **General E(r)**, for malnormal `Y ≤ F_r` of rank `r`. This is needed for
  (RI) at `k = 1` over every malnormal rank-2 host, because `Y = J ∩ B` can
  have any rank.
* **`k ≥ 2`.** Lemma R still reduces to the top case, but the SHN rank bound no
  longer pins `rk Y`.
* **(RI) versus (O).** (RI_{L_j}) ⇒ (G_j) ⇒ (O). A counterexample to (RI)
  would not by itself refute (O).

Class-killing consequence for future hunts: **any search for a top-case
violation of (RI_{L_j}) or (Mon_φ) must use non-nilpotent, non-extendable
quotients.** Homology, p-group and nilpotent certificates are provably blind
there. Every non-extendable kernel for S3, A4, S4 and A5 has been exhausted up
to the lengths above.

## Proposed `## Attempts` entry for the target (for the lander)

The worktree copy of the target node is stale relative to the swarm branch, so
this worker did not edit it. Proposed text:

> **swarm-0917-w19-w19-fp-follow (host-geometry, 2026-09-19)**, OPEN. See
> [fpbs-overfold-malnormal-ri-overgroup-2026-09-19](artifacts/fpbs-overfold-malnormal-ri-overgroup-2026-09-19.md).
> Proved:
>
> * **(R)** For malnormal rank-2 `B`, (RI_B) at `k = 1` reduces, via strengthened
>   Hanna Neumann, to the equal-rank top case E(r).
> * **(N)** Extendable quotients cannot certify an (RI) violation.
> * **(N1)** `L_j ↪ F` is an `H_1`-isomorphism, so every nilpotent, p-group or
>   homology certificate is blind in the top case `J ⊇ L_j`.
> * **(O)** The only rank-2 overgroups of `L_1` are `L_1` and `F`.
> * **(Mon_φ)** The `J = F` case of (RI_{L_1}) is `rk(F : X_0) ≤ rk(F : φX_0)`.
> * (RI_{L_j}) ⇒ (G_j) ⇒ (O).
>
> Computed: every non-extendable kernel of `L_1 → S3, A4, S4, A5` against all
> `g` up to lengths 12, 11, 9 and 8 gives 0 violations. Random malnormal hosts
> give 0 of 321 kernels, against 15 of 142 for non-malnormal hosts. Conjecture
> (W) holds in 185 of 185 cases. Next: prove (W) or E(2) for `L_1`.
