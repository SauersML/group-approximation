# Leavitt path algebra and Steinberg algebra hosts for Boone--Higman, 2026-09-12

Lane `bh-leavitt-path-steinberg` (Boone--Higman swarm). Boone--Higman stays open.

**Scope and ownership.** This lane owns hosts built from Leavitt path algebras of
finite graphs, Steinberg algebras of ample groupoids, and topological full groups
of ample groupoids (Matui's one-sided SFT full groups, Nekrashevych and
Röver--Nekrashevych groups as groupoid full groups). Twisted Brin--Thompson hosts
belong to `bh-twisted-brin-thompson`.

**Results.**
1. *K-theory (Theorem A, proved).* For a finite graph `E` with no sinks and no
   sources and `D = det(1 - N_E^t)`, the low and higher K-groups of `L_(F_q)(E)`
   are decided by the arithmetic of `D`. Over `F_2`: `K_2 = 0` always,
   `K_1 = 0` iff `D != 0`, and all `K_n`, `n >= 1`, vanish iff `D = ±2^k`.
2. *Division (Theorem B, proved).* If `E` is finite, sinkless, cofinal and
   satisfies condition (L), every finite family of nonzero elements of
   `L_K(E)` admits one common right multiplier `X` and left inverses `u_i` with
   `u_i a_i X = 1`. This is the input Khanh's frame-extension step needs.
3. *Host theorem (open, two citations missing).* Over `F_2`, with `[1] = 0` in
   `K_0` and `D != 0`, the Khanh--transfer argument of
   `research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md` should run
   verbatim with Theorem B in place of its Lemma 2.2. The unwritten inputs are
   cancellation in `V(L(E))` and the centre of `L(E)`.
4. *Example.* The two-vertex graph with `N = [[2,3],[1,2]]` has `K_0 = Z/2`,
   `[1] = 0`, `D = -2`, and every `K_n`, `n >= 1`, zero over `F_2`. So it is a
   candidate acyclic host that is not isomorphic to `L_2`.
5. *What this does and does not buy for Boone--Higman* (Section 5). Every such host
   contains `L_2` unitally, so no new Boone--Higman class follows yet.

## 0. Khanh's criteria, as verified elsewhere

Quoted in the reviewed artifact `boone-higman-leavitt-tensor-hosts-2026-09-12.md`
from the PDF of arXiv:2609.08428v1 (text on MSI,
`/projects/standard/hsiehph/sauer354/lit-groups/khanh-clean.txt`):

- **Theorem 2.2** (acyclicity criterion), for nonzero unital `F_2`-algebras `A`
  with `A^2 ≅ A` as right modules: if (1) standard inclusions kill `H_n` and
  (2) `H̃_i(X_r(A)) = 0` for `0 <= i <= r-3`, `r >= 4`, then `H_n(A^x) = 0`.
- **Theorem 5.1** (Steinberg criterion), for every nonzero unital ring `B` of
  characteristic two and `n >= 4`: if (1) `GL_(n-1) = E_(n-1)`, `GL_(n-2) = E_(n-2)`,
  (2) `j_(n-1)(N_(n-1)(B)) = 1` in `St_n(B)`, (3) `|X_n(B)|` simply connected, then
  `St_n(B) -> GL_n(B)` is an isomorphism. The prime-field artifact signs the
  transporters for odd `p`.

The ring properties the transfer uses are therefore:

| Property | Used for |
|---|---|
| (P1) `A^2 ≅ A` (a unital Leavitt family `e,f`) | Theorem 2.2, compression `c(u) = e u e* + f f*`, leaf coordinates `A ≅ M_m(A)` |
| (P2) simultaneous strong division, complements of the right size | frame extension (Khanh Prop 4.2), hence (2) and (3) above |
| (P3) `K_1(A) = K_2(A) = 0` (all `K_n`, `n >= 1`, for acyclicity) | stable input of Prop 3.1; `GL = E`, `H_1 = H_2 = 0` |
| (P4) `A` finitely presented as a ring | Krstić--McCool, finite presentation of `A^x ≅ St_5(A)` |
| (P5) strong division, trivial central units | the Lean root-detection theorem, simplicity of `E_n(A)` |

## 1. Theorem A: K-theory of Leavitt path algebras over finite fields

**Source.** Ara--Brustenga--Cortiñas, arXiv:0903.0056v2 (text on MSI,
`.../lit-groups/abc-clean.txt`), read 2026-09-12:

> Theorem 7.6. Let k be a regular supercoherent ring and let E be a row-finite
> quiver. Then K(L_k(E)) = hocofiber(K(k)^(E^0 \ Sink(E)) --(1 - N_E^t)-->
> K(k)^(E^0)). It follows that there is a long exact sequence
> K_n(k)^(E^0 \ Sink(E)) --(1 - N_E^t)--> K_n(k)^(E^0) -> K_n(L_k(E)) ->
> K_(n-1)(k)^(E^0 \ Sink(E)) -> ...

with `N_E = (n_ij)`, `n_ij = #{arrows from i to j}`, and sink columns removed.
The introduction states that fields are regular supercoherent.

**Convention.** ABC discuss two incidence conventions (their Section 4). For a
finite graph with **no sinks and no sources** the matrix is square, and the two
conventions differ by a transpose. A square integer matrix and its transpose
have the same determinant and the same Smith normal form, so everything below is
convention-free.

**Quillen's computation** (Ann. of Math. 96, 1972; classical, not re-read here):
`K_0(F_q) = Z`, `K_(2i-1)(F_q) = Z/(q^i - 1)` and `K_(2i)(F_q) = 0` for `i >= 1`.

**Theorem A.** Let `q = p^f`, let `E` be a finite graph with no sinks and no
sources, and put `T = 1 - N_E^t` and `D = det T`.
1. `K_1(L_(F_q)(E)) = 0` iff `D != 0` and `gcd(D, q-1) = 1`.
2. `K_2(L_(F_q)(E)) = 0` iff `gcd(D, q-1) = 1`.
3. `K_n(L_(F_q)(E)) = 0` for every `n >= 1` iff `D = ±p^k` for some `k >= 0`.
4. If `D != 0`, `K_0(L_(F_q)(E)) = coker(T : Z^V -> Z^V)` has order `|D|`.

*Proof.* The long exact sequence breaks into short exact sequences
`0 -> coker(T | K_n(F_q)^V) -> K_n(L) -> ker(T | K_(n-1)(F_q)^V) -> 0`.
- On `Z^V`, `T` is injective iff `D != 0`, and then `|coker T| = |D|`.
- On a finite module `(Z/m)^V`, `T` is injective iff surjective iff `D` is a unit
  mod `m`, using the adjugate.
- `n = 1`: coker on `(Z/(q-1))^V`, ker on `Z^V`. `n = 2`: `K_2(F_q) = 0`, ker on
  `(Z/(q-1))^V`. Odd `n = 2i-1` and even `n = 2i` both reduce to `D` a unit mod
  `q^i - 1`.
- A prime `ℓ != p` divides `q^i - 1` for `i` the order of `q` mod `ℓ`, and `p`
  divides no `q^i - 1`. So `gcd(D, q^i - 1) = 1` for all `i >= 1` iff every prime
  factor of `D` is `p`. `∎`

**Over `F_2`.** `q - 1 = 1`, so `K_2 = 0` for every sinkless sourceless finite
graph, `K_1 = 0` iff `D != 0`, and the host is K-acyclic in degrees `>= 1` iff
`D = ±2^k`.

**Examples over `F_2`.**
- `E_2`, one vertex with two loops: `D = -1`. This is `L_2`; Ara--Cortiñas already
  give `K_*(L_2) = 0`.
- The Cuntz splice of `E_2`: `D = +1`, `K_0 = 0`.
- One vertex with `n` loops: `D = 1 - n`, `K_0 = Z/(n-1)` with `[1]` a generator.
  K-acyclic in degrees `>= 1` iff `n - 1` is a power of two, but `[1] != 0` unless
  `n = 2`, so (P1) fails for `n >= 3`.
- Two vertices, `N = [[2,3],[1,2]]` (two loops at each vertex, three edges
  `v1 -> v2`, one edge `v2 -> v1`). Then `T = [[-1,-1],[-3,-1]]`, `D = -2`, and
  `K_0 = Z/2`. The class `[1] = (1,1) = -(second column)` lies in the image, so
  `[1] = 0`. All `K_n`, `n >= 1`, vanish over `F_2`. The graph is strongly
  connected and every cycle has an exit.

## 2. Theorem B: simultaneous strong division in `L_K(E)`

Conventions: CK1 `e* f = δ_(e,f) r(e)`, CK2 `v = Σ_(s(e)=v) e e*` for every vertex
`v` emitting edges. Paths are linearly independent in `L_K(E)`.

**Theorem B.** Let `K` be a field and `E` a finite graph with no sinks that is
cofinal (every vertex connects to every cycle) and satisfies condition (L) (every
cycle has an exit). For nonzero `a_1, ..., a_s` in `L = L_K(E)` there are `X` and
`u_1, ..., u_s` in `L` with `u_i a_i X = 1` for every `i`.

*Proof.* Fix a cycle `C` based at `c_0` (length `|C|`), an exit `ε` from a vertex
`x` of `C`, the arc `α` of `C` from `c_0` to `x` (`|α| < |C|`), and a path `ρ` from
`r(ε)` to `c_0`. `ρ` exists by cofinality.

1. **Reduce to the path algebra.** Choose `N` at least every `|μ|` in expressions
   `a_i = Σ c λ μ*`. With no sinks, iterating CK2 gives `1 = Σ_(|γ| = N) γ γ*`.
   - `μ* γ` is the remainder path or `0`, so each `a_i γ` is a combination of real
     paths, all ending at `r(γ)`.
   - `a_i = Σ_γ (a_i γ) γ*`, so some `a_i γ != 0`.
2. **Separate the blocks.** Let `Λ` bound all path lengths in all `a_i γ`. From every
   vertex `w` there are paths to `c_0` of every length `d_w + k|C|`, `k >= 0`.
   - Choose paths `τ_γ` from `r(γ)` to `c_0` whose lengths `ℓ_γ` make the intervals
     `[ℓ_γ, ℓ_γ + Λ]` pairwise disjoint.
   - Put `x_0 = Σ_γ γ τ_γ`. Then `P_i = a_i x_0 = Σ_γ (a_i γ) τ_γ`.
   - Concatenation with a fixed `τ_γ` is injective and the length ranges are
     disjoint, so no coefficients combine: `P_i != 0`.
   - Every path in the support of `P_i` ends at `c_0`.
3. **Antichain.** Let `Λ'` bound the support lengths of all `P_i`, pick `k` with
   `k|C| > Λ'`, and put `τ = C^k α ε ρ` and `x = x_0 τ`.
   - For support paths `ν != ν'` with `|ν| = |ν'|`, `ντ` and `ν'τ` differ in the
     first `|ν|` edges.
   - If `|ν| < |ν'|`, position `p = |ν| + k|C| + |α| + 1` of `ντ` carries `ε`.
     Since `|ν'| < p <= |ν'| + k|C| + |α|`, position `p` of `ν'τ` lies in its
     `C^k α` block, whose edges belong to `C`. So `ντ` and `ν'τ` are incomparable.
   - Pick `η_i` in the support of `P_i τ` with coefficient `c_i != 0`. Incomparable
     paths annihilate under `η* ν`, and `η_i* η_i = r(τ) = c_0`, so
     `η_i* a_i x = c_i c_0`.
4. **`1 ≲ c_0`, explicitly.** Take `M >= |E^0|`. Every path `γ` of length `M`
   repeats a vertex among its first `|E^0| + 1` vertices, so it passes through a
   vertex on a cycle. Cofinality lets `c_0` reach that cycle, hence `r(γ)`: choose
   a path `μ_γ` from `c_0` to `r(γ)`.
   - The paths `π_j = C^j α ε ρ`, `j = 1, 2, ...`, are pairwise incomparable loops
     at `c_0`, by the same position argument, and `π_j* π_j = c_0`.
   - Enumerate the length-`M` paths `γ_1, ..., γ_T` and put
     `S = Σ_j π_j μ_(γ_j) γ_j*`. Then `S = c_0 S` and
     `S* S = Σ_j γ_j μ_j* c_0 μ_j γ_j* = Σ_j γ_j γ_j* = 1`.
   - So `t = S*` and `s = S` satisfy `t c_0 s = 1`.
5. **Assemble.** Put `X = x s` and `u_i = c_i^(-1) t η_i*`. Then
   `u_i a_i X = c_i^(-1) t (c_i c_0) s = 1`. `∎`

The case `s = 1` is strong division, `x != 0 => a x b = 1`. The hypotheses are
those of simplicity of `L_K(E)` for sinkless finite `E` (Abrams--Aranda Pino); the
proof uses the graph conditions directly and cites nothing.

## 3. The host theorem over `F_2` (open)

**Target.** Let `E` be finite, sinkless, sourceless, cofinal, with condition (L).
Put `L = L_(F_2)(E)` and `D = det(1 - N_E^t)`, and assume `[1_L] = 0` in `K_0(L)`
and `D != 0`. Then:
- `GL_m(L) = E_m(L)` for `m >= 2`, and `H_1`, `H_2` of every `GL_r(L)` vanish;
- `St_r(L) ≅ GL_r(L)` for `r >= 3`;
- `L^x` is finitely presented and simple;
- if `D = ±2^k`, every `GL_r(L)` is integrally acyclic.

**What is proved.** (P3) is Theorem A. (P2), in its multiplier form, is Theorem B.
(P4): a finite graph gives a finite presentation of `L` over `F_2`.

**What is missing.**
- **(P1) and complement sizes need cancellation.** `[1] = 0` gives `2[1] = [1]` in
  `K_0`. Turning that into `L ≅ L^2`, and identifying every nonzero f.g. projective
  of class `0` with `L`, needs `V(L)* = K_0(L)` for purely infinite simple `L`.
  Expected source: Ara--Goodearl--Pardo (K-Theory 2002) together with
  Ara--Moreno--Pardo (`V(L(E)) = M_E`). Not verified here. In Theorem B the kernel
  of `u_i` has class `[1] - [c_0] + [c_0] - [1] = 0`, so cancellation is exactly
  what makes it `≅ L`.
- **(P5) needs `Z(L) = F_2`.** Expected source: Aranda Pino--Crow, centre of a
  simple Leavitt path algebra. Not verified. The repo's internal kill-word proof
  covers only `L_k(1,2)`.

With both, the transfer of `boone-higman-leavitt-tensor-hosts-2026-09-12.md`
Sections 2--4 applies line by line, with Theorem B replacing its Lemma 2.2 and
Theorem A replacing the K-hypothesis. That transfer is a paper argument and has not
been reviewed.

## 4. Topological full groups and Steinberg algebras

- **Monomial units.** Units of `L_K(E)` of the form `Σ α_i β_i*` (prefix-code
  bijections of the path space) form the topological full group of the graph
  groupoid. For `E_2` this is `V`. So `[[G_E]] <= L_K(E)^x`, and a graph host
  contains the SFT full group as its monomial part.
- **Beyond graphs.** For Steinberg algebras `A_K(G)` of other minimal effective
  ample groupoids (Nekrashevych algebras of self-similar groups, groupoids of
  rational similarity groups), no ABC-type K-theory sequence is available.
  (P2)--(P4) would each have to be proved from scratch, and simplicity can depend
  on the characteristic, as recalled from Clark--Exel--Pardo--Sims--Starling for
  the Grigorchuk group's algebra in characteristic two. That is not verified here
  and is recorded only as a warning for characteristic-2 hosts.
- **Weyl obstruction.** `weyl-algebra-blocks-a-universal-leavitt-host` quotes
  Bilich--Hazrat--Nam: the Heisenberg equation is unrealizable in Steinberg
  algebras. Over a field of characteristic `p`, `M_p(F_p)` (a Steinberg algebra
  of a finite pair groupoid) contains solutions of `xy - yx = 1`, so that
  statement must carry a characteristic-zero hypothesis. The node should be
  checked against the source before any characteristic-2 host argument relies on
  it.

## 5. What graph hosts buy for Boone--Higman

- Every host of Section 3 satisfies `[1] = 0`, hence contains `L_2` unitally
  once cancellation holds. So `L_2^x <= L^x`, and every group already embedded
  in `L_2^x` or `(L_2 ⊗ L_2)^x` embeds again: nothing new on that side.
- The new content is structural. There is an infinite family of candidate
  finitely presented simple groups, parametrised by finite abelian `K_0` with
  `[1] = 0` and the sign of `D`. It contains non-isomorphic rings, e.g.
  `K_0 = Z/2` above against `K_0 = 0` for `L_2`. A template (P1)--(P5) for
  Steinberg-algebra hosts also follows.
- A new Boone--Higman class would need a host whose coefficient subalgebras reach
  beyond `F_2[t_1, t_2]`-type commutative pieces. That is
  `bh-decidable-algebra-hosts`'s premise and `leavitt-tensor-k-theory`'s tensor
  powers, not graph algebras.
