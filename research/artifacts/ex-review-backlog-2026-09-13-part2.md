# EX review, backlog, part 2: the weak-soficity collapse and width theorems, and the VTF triangle lane (2026-09-13)

Lane `ex-verify-backlog`. Index: `ex-review-backlog-2026-09-13.md`.

## 2. ex-weak-soficity

Landings: 13562b357e, 57fdcf7cf3, 4656ff0c3d, 620c45997e, 022f911f8e, 604cc0a50f, 9054eb0d3f,
4d3da81924, 4e7e23aa0d.

### 2.1 `simple-group-support-and-semisimple-rank-models-collapse`: PASS, one justification repaired

Re-derived:
- **Lemma 1.2.**
  - Restricting to `Ω_0` changes no supports.
  - By the union bound some generator has `|supp| >= |Ω_0|/|X|`.
  - The Hamming ultraproduct homomorphism is nontrivial, and simplicity makes it injective. Elek--Szabó
    then applies.
  - If `|Ω_0^(n)|` stays bounded, relator supports are eventually empty. The tuples are then nontrivial
    homomorphisms to finite groups, which an infinite simple group does not have.
- **Item 1.** With `k = ⌈1/ε_0⌉`, `1 <= f(t) <= f(k⌈ε_0 t⌉) <= k f(|supp r(a)|) <= kε`.
- **Lemma 2.2.**
  - In a basis adapted to `U = ∩_x ker(a_x - 1)`, `a_x - 1 = [[0,N],[0,D]]` and
    `a_x^(-1) - 1 = [[0, -N(1+D)^(-1)],[0, -D(1+D)^(-1)]]`.
  - Since `N(1+D)^(-1) = N - N D (1+D)^(-1)`, `rk E' <= 2ηM`.
  - `N̂_i N̂_j = 0`, and telescoping gives `rk E_w <= 2 L_w η M`.
  - The identity `Σ_r c_(x,r) e_(r,y) = δ_(x,y)` recovers `N̂_x`.
- **Lemma 2.3.**
  - With `η = 1/(4|R|L+2)`, the conclusion of 2.2 reads `M <= |R|δM + M/2`, which fails once
    `|R|δ < 1/4`.
  - On `V/U`, the moved generator has normalized rank `>= η/|X|`, and the relators have normalized rank
    `< δ_n/η`.
- **Item 4.**
  - `Ad(g) - 1` is `A ↦ (BA - AB) g^(-1)`, of rank `<= 2nρ`.
  - `n² - dim C(g) >= n min(ρ, n/2)`, from `dim C(g) = Σ_λ Σ_j (μ'_(λ,j))²`, bounded by the largest
    geometric multiplicity times `n`.

**Finding (justification, no verdict change).** Item 4 bounds the multiplicity at an eigenvalue `λ` outside
`F` by "a Galois conjugate has the same multiplicity".
- This does not cover purely inseparable `λ` over an imperfect field. For example `F = F_2(t)` and
  `λ = √t`, which has no other conjugate.
- The bound `n/2` still holds. Let `m` be the minimal polynomial of `λ` over `F`. Each Jordan block at
  `λ` comes from exactly one cyclic summand `F[x]/(m^k)` of the `m`-primary part, and that summand has
  `F`-dimension `>= deg m >= 2`.
- Corrected forward on the route.

### 2.2 `simple-group-relator-width-in-finite-simple-targets`: PASS, one exponent corrected

- **(E1), (E2).** A finite image of an infinite simple group is trivial. A shortest product of conjugates
  has distinct partial products.
- **(A).**
  - `C[S]` has exactly one trivial summand, since `S` is one orbit, and a nontrivial irreducible
    constituent. So `|S| - 1 >= c q^(rk Q)`.
  - The route wrote `c q^rho`, but `rk Q` may be smaller than the bound `rho`.
  - The argument needs only `|S| >= c q`, which gives `log|Q|/log|S| <= 2D(ρ)` once `q >= c^(-2)`.
  - Corrected forward on the route.
- **(B), symmetric targets.**
  - `|C| = n'!/((n'-s)! Π j^(c_j) c_j!)`, and `c_j! <= (s/j)^(c_j)` gives `Π <= s^(s/2)`. Hence
    `log|C| >= (s/2) log s - s`.
  - `N_0 = ⌈e^8 ε_0^(-4)⌉` covers both needs: `n' >= ε_0^(-4)` gives `log s >= (3/4) log n'`, and
    `n' >= e^8` gives `s <= (s/8) log n'`.
  - `k > 24/ε_0` gives `|C|^k > n'^(6n')`, and Rodgers applies for `n' >= 5`.
  - Parity: a sign map that killed every relator value would kill every generator, by (E1).
- **(B), alternating targets.** `|S| >= |C|/2`, so `S^k = Alt(Ω_0)` for `k >= 8c/ε_0`.
- **Converse of (B), and (C).** Bi-invariance and the triangle inequality.
- **Citations, checked** in the lane's MSI extractions:
  - `mp.txt`, lines 16--18 (Liebeck--Shalev) and 28--31 (Rodgers, `n^6(n−2)`);
  - `np.txt`, line 87 ("rank r over Fq we have k ≥ cq^r").
  - These are secondary quotes. The primary papers were not re-read, as the citation route says.

### 2.3 `perfect-group-relator-width-over-nilpotent-groups`: PASS

- **Base.** With all conjugators `1`, the template is `Π r^(n_r)`, and the pairs `r · r^(-1)` cancel.
- **Step.**
  - `(c''d) r^(-1) (c''d)^(-1) = (c'' r^(-1) c''^(-1)) · c''[r,d]c''^(-1)`, with `[a,b] = a b a^(-1) b^(-1)`.
  - `[r, d_r]` lies in `γ_j`, has image `[e_r, W_r]`, and is central modulo `γ_(j+1)`.
  - `-u = Σ_r [e_r, W_r]` is solvable because `L_j` is additively spanned by `[L_1, L_(j-1)]` and the
    `e_r` span `L_1`.
- The pattern and the count `K(x)` never change. Only the conjugators accumulate.

### 2.4 `residually-finite-doubles-are-weakly-sofic`: PASS, conditional on the Glebsky import

- The fold kernel meets every conjugate of a vertex group trivially, so it is free.
- In the free-lamp amalgam, edge stabilizers are trivial. So the kernel is a free product of conjugates of
  `K` and a free group. It is residually finite for any number of factors, by retraction onto finitely
  many.
- Glebsky Theorem 1.1 is used as quoted in `weakly-sofic-not-sofic-proof`. I did not re-read it.

### 2.5 Graph status

- **OPEN, with Attempts:**
  - `non-weakly-sofic-group-exists`;
  - `fg-simple-weakly-sofic-groups-are-sofic`;
  - `binary-leavitt-unit-group-is-weakly-sofic`;
  - `non-linear-sofic-simple-groups-bounded-width-in-classical-groups`.
- `non-weakly-sofic-group-from-simple-weak-sofic-rigidity` requires the open rigidity claim, so it does
  not fire.
- **Queued, not yet reviewed:** `howie-pro-p-tuple-fails-the-profinite-certificate-at-a5`.

## 3. ex-hyperbolic-vtf, beyond the Chern--Quillen chain

The Chern--Quillen chain was passed earlier, in `ex-review-groups-2026-09-12-part2.md` §2.1.

### 3.1 `simple-vertex-groups-vtf-iff-some-finite-quotient` (54faf1cd64, 5a34c7f6f4): PASS

- **Lemma.** A non-injective restriction to a simple `A_i` kills `A_i`. Connectivity spreads this to all
  vertex groups.
- **(<=).** The criterion node is not needed. A finite quotient that is injective on every finite subgroup
  has torsion-free kernel.
- **Citation note.** CCKW Theorem 3.1 assumes the vertex groups are generated by their two edge groups.
  - In general, developability and the fixed-point step rest on Bridson--Haefliger II.12.28, which neither
    the lane nor I re-read.
  - The random `(A_7, A_7, A_8)` candidates use generating pairs, so CCKW covers them.

### 3.2 `non-vtf-hyperbolic-counterexample-may-be-one-ended` (b6178d5340): PASS

- `G_e ∩ N_v = 1`, because `G_e` is finite and `N_v` is torsion-free.
- The graph of finite groups `G_v/N_v` has virtually free fundamental group, and `ψ` is injective on its
  vertex groups.
- `ker φ ∩ g G_v g^(-1) = g N_v g^(-1)`, and every finite subgroup fixes a vertex.
- **Corollary.** Dunwoody accessibility, plus quasiconvexity of vertex groups over finite edge groups.

### 3.3 `lattice-forced-torsion-dies-in-hyperbolic-quotients` and its dead route: PASS

- **Item 1.** `π(N) = 1` would kill `<<N>>`. So `π(N)` is a nontrivial quotient of `N` with no nontrivial
  finite quotient, and `Q` is not residually finite.
- **Item 2.** Simplicity makes `π|_N` injective or trivial, and a hyperbolic group contains no `Z²`.
- **Item 3.** Uses `kapovich-wise-rf-iff-finite-quotients`, whose citation route has `requires: []`.
- The invalidator is established, so `non-vtf-hyperbolic-via-lattice-forced-torsion-quotient` is correctly
  dead.

### 3.4 Code-based claims (211f38c8e1, e18d2ec38d): labelling PASS, support argument PASS, code not rerun

- **Labelling.** The artifact says "decides nothing". The four zero counts appear only as Attempt data in
  the OPEN `hyperbolic-simple-triangle-group-without-finite-quotients`. No negative search result is
  stated as established.
- **§4 support argument, re-derived.**
  - For `n <= 13`, an `A_7` inside `A_n` has orbits of sizes 1 and 7 only, since the next transitive
    degree is 15. It has at most one orbit of size 7.
  - So `φ(A)` and `φ(B)` act naturally on `supp φ(q)`.
  - Then `φ(p)` and `φ(r)` lie in `Alt(supp φ(q))`, of order `2520 < |A_8|`.
  - So the zeros into `A_8`--`A_13` are forced, as the artifact says.
- **§5 nonexistence, a shorter form of the parity count.**
  - The face `D_8` lies in all three edge groups.
  - The `O_2` of each edge group is one of the two Klein four-subgroups of `D_8`.
  - At each vertex, the two edges have different `O_2`.
  - A triangle cannot be 2-coloured, so no such triangle of groups exists.
  - This is artifact content only; no node carries it.
- **Moore bounds.** 43 and 259 check.
- **The search method.**
  - Every nontrivial map is vertex-injective and is enumerated up to `C_S(p)`, so the method is complete.
  - The GAP runs were not repeated.
