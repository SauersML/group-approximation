# Sigma^m of bF_{n,r}: what the character computation decides

Lane z2-13-pure-braided-bht, 2026-09-13. Unreviewed. Part 2; notation from
`zp-pure-braided-bht-characters-2026-09-13.md` (`W`, types, `tau_phi`, `W_0`).

## 1. Tools

As quoted in Zaremsky arXiv:1803.02717 (re-read verbatim from the originals before any Lean or citation route):

- (T1) Citation 1.8 = Meier–Meinert–VanWyk [MMV01, Theorem 2.4]: "Let G be a group acting cocompactly on an
  (m−1)-connected complex X. Let χ ∈ Hom(G,ℝ) be a character such that for any cell σ in X with dimension
  dim(σ) ≤ m, the restriction χ|Stab_G(σ) is non-trivial. If for all σ with dim(σ) < m, we have that
  Stab_G(σ) is of type F_{m−dim(σ)} and [χ|Stab_G(σ)] ∈ Σ^{m−dim(σ)}(G_σ), then [χ] ∈ Σ^m(G)."
- (T2) Citation 1.12 = [MMV01, Theorem 2.1]: "Let G be a group of type F_m and let χ ∈ Hom(G,ℝ). If
  χ(Z(G)) ≠ 0 then [χ] ∈ Σ^m(G)."
- (T3) Citation 1.9 = Meinert [Mei97, Corollary 2.8]: "Let π: G → H be a split epimorphism of groups. Let χ be
  a character of H, so χ∘π is a character of G. For any m ≥ 1, if [χ∘π] ∈ Σ^m(G) then [χ] ∈ Σ^m(H)."
- (T4) Skipper–Wu arXiv:2103.14589 (extraction; numbers to re-check): the Stein space `X` of `bF_{d,r}(H)` is
  the contractible cubical complex of dangling pure `r`-spraiges; the height `f` = number of feet, and every cell
  has a unique `f`-maximal vertex; `X^{f <= m}` is finite modulo the group (Proposition 4.6); the stabilizer of a
  cube `[x, y]` (with `y` an elementary expansion of `x`) is `B^J_m(H)` (Proposition 4.8), for pure braids and
  `H = 1` the pure braid group on the feet of `x`; descending links are linear arc matching complexes, at least
  `(floor((m - d)/(3d - 2)) - 1)`-connected at height `m` (Corollary 4.15); Theorem 4.29 gives `F_n` iff `H` is.
  Skipper–Wu write `d` for the arity; here the arity is `n` and `d = n - 1`. With `H = 1` their group is `bF_{n,r}`.
- (T5) Zaremsky arXiv:1502.02620, Theorem A for `F_n` = PL homeomorphisms of `[0,1]` with slopes in `<n>` and
  breakpoints in `Z[1/n]`: for `m >= 2`, `a chi_0 + sum c_i psi_i + b chi_1` is not in `Sigma^m(F_n)` iff all
  `c_i = 0` and `a, b >= 0`; `chi_0, chi_1` are the first- and last-leaf depth characters.

## 2. Theorem 3: characters seen by full twists lie in Sigma^infinity

**Theorem 3.** Let `chi = pi^* psi + phi` with `psi` in `Hom(F_{n,r}, R)` arbitrary and `phi` in `W` with
`tau_phi` not identically zero on large `k`. Then `[chi]` is in `Sigma^infinity(bF_{n,r})`.

*Proof.* Fix `j`.
(a) By Proposition 2, `tau_phi(k) != 0` for all `k >= p`, some `p`.
(b) The ascending link of a vertex `x` (cubes in which `x` is the bottom vertex: expand a nonempty subset of the
feet of `x`) is a simplex on the feet, so contractible. By the Morse lemma for the height `f`,
`X^{f >= p} -> X` is a homotopy equivalence; `X` is contractible (T4).
(c) A descending neighbour `y` of `x` merges disjoint blocks of `n` feet, so `f(y) >= f(x) - (n-1) f(x)/n
= f(x)/n`. Take `q >= n p` so large that descending links at heights `> q` are `(j-1)`-connected (T4). Adding
the vertices of height `> q` to `X^{p <= f <= q}` in increasing height glues along full descending links, so the
inclusion into `X^{f >= p}` is `j`-connected, and the band `X^{p <= f <= q}` is `(j-1)`-connected.
(d) The band is cocompact (T4, Proposition 4.6).
(e) The stabilizer of a cube is the stabilizer of its bottom vertex `x` (T4, Proposition 4.8 with `H = 1`),
a conjugate `g {(S, b, S) : b in PB_{f(x)}} g^{-1}` for a forest `S` with `f(x)` leaves. Its center contains
`g z_S g^{-1}`, `z_S = (S, Delta^2, S)`, and `chi(g z_S g^{-1}) = phi(z_S) = tau_phi(f(x)) != 0` since
`f(x) >= p` (§4 of part 1: the value depends only on the number of leaves). So `chi` restricts nontrivially to
every cell stabilizer, the stabilizers are of type `F`, and (T2) puts each restriction in `Sigma^infinity`.
(f) (T1) gives `[chi]` in `Sigma^j(bF_{n,r})`. As `j` is arbitrary, `[chi]` is in `Sigma^infinity`. ∎

For `n = 2`, `r = 1`, `tau(k) = omega_0 + (k-1) omega_1`, and Theorem 3 is Case 1 of the proof of Zaremsky's
Theorem 5.1 (arXiv:1803.02717), which uses `X^{2q <= h <= 4q}` in the same way. Since `W_0 = 0` for `n = 2`,
Theorem 3 covers every character with a nonzero braid component there; for `n >= 3` it covers all of them except
those whose braid component lies in the `n(n-1) - 2`-dimensional `W_0`.

## 3. Proposition 4: holes of F_{n,r} pull back

**Proposition 4.** For `psi` in `Hom(F_{n,r}, R)` and `m >= 1`: if `[pi^* psi]` is in `Sigma^m(bF_{n,r})`
then `[psi]` is in `Sigma^m(F_{n,r})`. If `r ≡ 1 mod (n-1)` and `m >= 2`, then `[pi^*(a chi_0 + b chi_1)]` is not
in `Sigma^m(bF_{n,r})` for `a, b >= 0`, not both zero.

*Proof.* `pi` splits, so (T3). For `r ≡ 1 mod (n-1)`, part 1 Lemma 2 gives a PL homeomorphism `h: [0,1] -> [0,r]`
with slopes in `<n>` and breakpoints in `Z[1/n]`; conjugation by `h` is an isomorphism `F_{n,1} -> F_{n,r}`
carrying germs at `0` and at the right endpoint to germs at `0` and `r`, hence `chi_0, chi_1` to `chi_0, chi_1`.
(T5) gives the holes for `F_{n,1}`. ∎

## 4. The crux: full-twist-invisible braid characters

**Lemma 5 (reduction).** Let `phi` in `W`, `phi != 0`, and write `Phi_k(A_{ij}) = phi(type(i, j, k))`, a character
of `PB_k`. If `[Phi_k]` is in `Sigma^j(PB_k)` for all large `k ≡ r mod (n-1)`, then `[pi^* psi + phi]` is in
`Sigma^j(bF_{n,r})` for every `psi`.

*Proof.* Steps (b)–(d) and (f) of Theorem 3, with (e) replaced by the hypothesis. `Phi_k != 0` for large `k`,
since every type occurs among index pairs of large forests. ∎

So the open part of the formula is: for `phi` in `W_0 \ {0}` (`n >= 3`), is `[Phi_k]` in `Sigma^j(PB_k)` for
`k >= K(j)`? These `Phi_k` kill the full twist, so (T2) says nothing, and this is a question about the higher
BNSR invariants of pure braid groups (Problem 1.9; Zaremsky arXiv:1507.08597 gives `Sigma^infinity(P_n) =
Sigma^{n-2}(P_n)` and separation results, not these characters).

**Example (`n = 3`).** `PPP(alpha, gamma) = (-1)^gamma`, `PEP ≡ 1/2`, `EPP = PPE = 0`, derived
`EEP = PEE = -1/2`, and `EPE = 1` if `r` is odd, `EPE = 1/2` if `r` is even. Then `tau(k) = 0` for every `k >= 3`
with `k ≡ r mod 2` (checked by hand for `k = 3, 5, 7` and `k = 4, 6`). For `r` odd, `k = 5`:
`Phi_5(A_12) = -1/2`, `A_15 = 1`, `A_23 = A_34 = 1/2`, `A_24 = -1`, `A_45 = -1/2`, other `A_ij = 0`, sum `0`.
(The constant term of `tau` depends on `k mod d`, so `W_0` depends on `r mod d`; its dimension does not.)

## 5. What remains for the full formula

- (N4) every `phi` in `W_0 \ {0}` gives `Sigma^infinity` membership (Lemma 5 reduces it to pure braid groups;
  a direct route at the level of `bF_{n,r}` needs central elements that are not full twists on all strands).
- (N5) a pulled-back `pi^* psi` lies in `Sigma^m(bF_{n,r})` iff `[psi]` lies in `Sigma^m(F_{n,r})`, and
  `Sigma^m(F_{n,r})` has the endpoint-hull form for every `r`. Proposition 4 gives one direction. For the other,
  `chi = pi^* psi` vanishes on all cell stabilizers, so (T1) does not apply; the natural route is Morse theory
  with `(chi, f)` on the Stein space (template: Zaremsky's proof of Theorem A, arXiv:1502.02620, with
  `(n-1)`-matching complexes replaced by Skipper–Wu's linear arc matching complexes with restricted foot sets),
  or for `n = 2` the HNN argument of Case 3 of Theorem 5.1 (arXiv:1803.02717).
