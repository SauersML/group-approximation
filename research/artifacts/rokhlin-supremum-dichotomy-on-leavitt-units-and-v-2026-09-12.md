# Rokhlin supremum dichotomy on the Leavitt units and Thompson's V (w7-rokhlin-dichotomy, 2026-09-12)

**Task.** Decide `h^Rok_sup = 0` or `= infinity` on `U = L_(F_2)(1,2)^x` or on `V = G_(2,1)`. Say what local sources
actually establish about Bernoulli Rokhlin entropy over nonsofic groups, and pin down the missing inequality.

**Outcome.** Both hosts remain undecided. Section 2 proves on every group that per-copy Bernoulli Rokhlin entropy is
zero or full, so every quantitative relaxation of a lower bound collapses to INF. Section 3 shows the self-copy
hypotheses decide nothing, orders the hosts, and localizes negative certificates. Section 6 states the exact missing
inequality as an OPEN claim on `V`. Nothing is refuted. All propositions are held OPEN until w4-vf-positive-b
re-derives them.

## 0. Imports and notation

- `h_sup(G) = sup h^Rok(X)` over free ergodic p.m.p. actions of finite Rokhlin entropy. POS, INF and RBS as in
  `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, item 1 (Theorem 1.10 of arXiv:1501.03367v4), for a countably
  infinite `G` and `H(L) < infinity`:

      h^Rok_G(L^G) = min{ H(L), h_sup(G) }.

- `Phi(k, E, F, psi)` and `rho_q(G) = lim_k h^Rok_G((A^k)^G)/k = inf Phi`, with `|A| = q`
  (`bernoulli-rokhlin-deficit-has-a-finitary-witness`).
- Theorem R, margin `mu = (j' - j) log|D|`, `Sigma = sum_i eta_i / D_i`, Proposition U' and Corollary U, all from
  `research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md`.
- Corollary A1 (`rokhlin-supremum-dichotomy-with-centralized-self-copies`): if `Gamma` contains `Gamma x Gamma` and
  finite subgroups of unbounded order, then `h_sup(Gamma) ∈ {0, infinity}`. Proposition 2.3 of
  `research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md` covers `U`. `V` is covered by
  `V_[0] x V_[1]` and `Sym(2^n)` (`thompson-v-has-positive-rokhlin-entropy-action`).

## 1. What local sources establish

1. **Positivity over nonsofic groups is open.** Seward, arXiv:1805.08279, introduction, as recorded in
   `every-group-has-positive-rokhlin-entropy-action`: "The Rokhlin entropy of the Bernoulli shift G↷(L^G,λ^G) is
   H(L,λ) when G is sofic but when G is not sofic its value is not yet known." By Theorem 1.10,
   `h^Rok(A^G) = min{log q, h_sup(G)}`, so "Bernoulli Rokhlin entropy > 0" is exactly POS(G).
   - It is proved for sofic groups (item 4 of the import).
   - It is open for every nonsofic group.
   - Every INF group known is sofic (quant-residue artifact, Scope).
   - Seward's factor-onto-Bernoulli theorem is not in the repository, so it is not used.
2. **Subgroups.** `bernoulli-rokhlin-maximality-passes-to-subgroups`: `h^Rok_G(L^G) <= h^Rok_H(L^H)` for infinite
   `H <= G`. So INF descends from `G` to `H`, and finiteness of `h_sup` ascends from `H` to `G`. Maximality ascends only
   in two cases:
   - up finite index (lines 201-202 of `research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md`);
   - from co-amenable subgroups (`rokhlin-maximality-ascends-co-amenable-subgroups`).
3. **Restrictions.** An `H`-generating partition is `G`-generating, so `h^Rok_G(X) <= h^Rok_H(X|_H)` for every
   `G`-action `X`. For infinite index, `L^G|_H` is Bernoulli over `H` with base `L^(H\G)`, so this bound is infinite.
   Restriction and co-induction give upper bounds only.
4. **Products.** Theorem 1.11 (item 3 of the import): if `P` has arbitrarily large finite subgroups and
   `h_sup(G) < infinity`, then `h_sup(P x G) = 0`. INF(`G x H`) gives INF(`G`) and INF(`H`) by item 2. The converse is
   not recorded locally.
5. **Self-copies.** `U <= U x U <= U` and item 2 give `h^Rok_(U x U)(L^(U x U)) = h^Rok_U(L^U)`, and the same holds for
   `V`. The embedding transports bounds in both directions but creates none. With the finite subgroups it yields
   Corollary A1 and nothing more (Section 3).

## 2. Per-copy entropy is zero or full on every group

**Proposition 2.1.** Let `G` be countably infinite, `|A| = q >= 2` and `k >= 1`. Then

    h^Rok_G((A^k)^G) = min{ k log q, h_sup(G) }.

Consequently:

- (a) `rho_q(G) ∈ {0, log q}`. It equals `log q` iff INF(G), and `0` iff `h_sup(G) < infinity`.
- (b) `inf Phi ∈ {0, log q}` at every `q`. A floor `Phi >= c` for one `c > 0` at one `q` gives INF(G), hence
  maximality at every alphabet.
- (c) If one configuration at one `q` and any `k` has `Phi < log q`, then for every `q' >= 2` and `eps > 0` some
  configuration at `q'` has `Phi < eps`.
- (d) Corollary 2(2) of `research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md` with any constant `C`
  gives INF(G), on every group. Domination (D) with a constant `C` self-improves to `C = 1`.
- (e) INF(G) iff `sup_k h^Rok_G((A^k)^G) = infinity`. Otherwise the deficit `k log q - h^Rok_G((A^k)^G)` equals
  `k log q - h_sup(G)` for `k >= h_sup(G)/log q`, and grows linearly.

*Proof.* The base `(A^k, uniform)` has `H = k log q < infinity`, so Theorem 1.10 gives the formula. Dividing by `k`
gives `min{log q, h_sup(G)/k}`, which tends to `log q` if `h_sup(G) = infinity` and to `0` otherwise. That is (a).

For (b), `rho_q = inf Phi` (Theorem 3 of the route artifact).

For (c), `inf Phi < log q` gives `rho_q < log q`, so `rho_q = 0` by (a). Then `h_sup(G) < infinity`, so
`rho_(q') = 0 = inf Phi` at `q'`.

For (d), Corollary 2(2) gives `rho_q >= log q/C > 0`, so `rho_q = log q` by (a), and Corollary 2(1) then gives (D).

(e) is read off the formula. QED.

**Remark 2.2 (no quantitative relaxation).** Over any countably infinite `G`, each of the following is equivalent to
INF(G):

- a floor `Phi >= c > 0` at one `q`;
- `h^Rok_G((A^k)^G) >= eps k` on an unbounded set of `k`;
- reverse restriction `h^Rok_G((A^k)^G) >= c h^Rok_H((A^k)^H)` for all `k`, from one infinite INF subgroup `H` with
  `c > 0`;
- domination with some constant `C`.

Each gives `rho_q > 0`, and INF gives each with `c = C = 1` (take `H` amenable, or `H = G`). So on `U` or `V` there is
no intermediate quantitative target in this family. A positive decision needs INF outright.

**Remark 2.3.** In `self-copy-host-rokhlin-deficits-need-unbounded-windows`, items 2 and 3 now hold on every group:
item 2 by (c), and item 3 by `bernoulli-witness-information-is-bounded-by-code-reads`. Only item 1 (`h_sup = 0`, the
case `k = 1`) uses the dichotomy. The "self-copy host" hypothesis in `rokhlin-window-transport-is-dominated` and at
line 74 of the random-order artifact is unnecessary.

## 3. Hosts

**Proposition 3.1 (Corollary A1 decides nothing).**

- (a) `⊕_N Z/2` satisfies A1, and it is amenable, hence INF.
- (b) For every countable `G`, `Gamma_G = ⊕_(n>=1) (G x Sym(n))` satisfies A1 and contains `G`.
- (c) So INF for every A1 host is equivalent to INF for every countably infinite group. `h_sup = 0` for some A1 host is
  equivalent to `h_sup(G) < infinity` for some `G`.

*Proof.* For (b), send summand `n` of the first factor of `Gamma_G x Gamma_G` into summand `2n`, and summand `n` of
the second into summand `2n+1`, using `Sym(n) <= Sym(2n)` and `Sym(n) <= Sym(2n+1)`. This is an injective
homomorphism. The groups `Sym(n)` are finite of unbounded order. Part (c) follows from INF descending (1.2) and from
A1. QED.

A decision on `U` or `V` must therefore use structure beyond A1. The tester-host route
`rokhlin-maximality-on-tester-covers-every-group` is the sharper form of (c).

**Proposition 3.2 (V inside U).** `V <= EL <= U` (`leavitt-cylinder-swaps-generate-thompson-in-el`). By 1.2 and the two
dichotomies:

- (a) POS(U) ⟹ INF(U) ⟹ INF(V) ⟹ POS(V);
- (b) `h_sup(V) = 0` ⟹ `h_sup(U) = 0`;
- (c) `V` sofic ⟹ INF(V). RBS allows bases of any finite entropy, so RBS ⟹ INF. Hence `h_sup(V) = 0` ⟹ `V` nonsofic.

The positive decision is cheapest on `V` and the negative one on `U`.

In the other direction, `U` has property (T) (`leavitt-unit-group-is-simple-fa-nonsofic`) and `V` has the Haagerup
property (`thompson-v-has-haagerup-property`). The standard incompatibility of the two for infinite groups (not
re-read locally, and used only in this remark) gives `U ≰ V`. So nothing moves from `V` up to `U` along inclusions.

## 4. Positive side: where each inequality points

1. **Sofic or amenable subgroups.** `h^Rok_G <= h^Rok_H`, the wrong direction. The reverse with any constant is INF
   itself (Remark 2.2).
2. **Co-amenable ascent.**
   - Over `U` it is empty (`simple-kazhdan-groups-have-no-proper-co-amenable-subgroups`).
   - Over `V`, no point stabilizer is co-amenable (`thompson-v-cantor-orbits-have-no-folner-sets`), and a co-amenable
     subgroup known to be maximal is sofic and makes `V` sofic (Attempts of
     `thompson-v-has-positive-rokhlin-entropy-action`).
3. **Compressions** (`iota_0`, `iota_1` on `U`; `V_[0]` on `V`). These have infinite index. Lemma 8.1 of
   arXiv:1602.06680v2 gives only `h_sub <= m h` at finite index `m`. At infinite index nothing follows (Attempts of
   `every-group-has-positive-rokhlin-entropy-action`).
4. **Theorem A spreading.** It turns `h_sup < infinity` into `0` and creates no lower bound. By Proposition 3.1 A1 is
   compatible with both sides.
5. **Koopman data, weak containment, cost, ℓ²-Betti numbers.** These do not depend on the base
   (`weak-invariants-give-no-bernoulli-rokhlin-lower-bound`, `koopman-lambda-singular-part-has-zero-rokhlin-entropy`).
6. **Codeword Følner count.** `Phi >= log q / lambda(F)` (`bernoulli-window-codeword-folner-ratio-bound`). Over `V`
   every configuration with amenable `<F F^-1>` is maximal. By 2.1(c) any deficit anywhere needs configurations with
   `lambda(F) -> infinity`, and `V ⊇ F_2 x F_2` has such `F`. No floor follows.
7. **w7-inf-cancellative** (domination for cancellative patterns). Not landed at tip `7e05aa7711`, so not cited as a
   result. By 2.1(d), any constant it proves would give INF on every group.

**Conclusion.** No positive result on `U` or `V`.

## 5. Negative side: constraints on a sub-threshold injection

Take `Phi` as in Theorem R over `G`, with margin `mu < Sigma`. Each `Y_i` misses a pattern `p_i` on `W_i`, and `M` is
the memory set.

**Proposition 5.1 (localization).** Put `H = <M ∪ W_1 ∪ ... ∪ W_n>`.

- (i) The same local rule gives an injective automaton `Phi_H` from `(B^n x D^j)^H` into
  `Y'_1 x ... x Y'_n x (D^(j'))^H`, where `Y'_i <= B^H` avoids `p_i` on `W_i`. The data `n, b, j, j', |D|, W_i` are
  unchanged, and so are `mu` and `Sigma`.
- (ii) Conversely, such an injection over any `H <= G` induces one over `G` with the same numbers.

Consequently:

- (a) `H` is infinite, since finite groups satisfy the margin bound (quant-residue artifact, Section 2);
- (b) `h_sup(H) < infinity` by Proposition U' over `H`, so `H` is not INF and is nonsofic;
- (c) over `U`, the windows generate a finitely generated nonsofic subgroup with finite `h_sup`, and they lie in no
  sofic subgroup. If they lie in `V`, they refute `thompson-v-has-positive-rokhlin-entropy-action` and make `V`
  nonsofic;
- (d) an injection below the threshold over `V` induces one over `U`.

*Proof.* `Phi(x)(g)` depends only on `x` over `gM <= gH`. Identify each left coset `gH` with `H` by `h ↦ gh`. Then
`Phi` acts coset by coset as `Phi_H`.

- Injectivity. If `Phi_H(z) = Phi_H(z')`, fill every other coset with one fixed configuration. The two outputs of
  `Phi` agree, so `z = z'`.
- Image. An occurrence of `p_i` at `h W_i` in `Phi_H(z)` would be an occurrence in `Phi(x)`.
- Converse. Apply the rule coset by coset. Every translate `g W_i` lies in one coset.
- Numbers. `D_i = |W_i W_i^-1|` is computed in any group containing `W_i`.

QED.

**Proposition 5.2 (track count).** Suppose every `Y_i` contains all constant configurations.

- Then `|W_i| >= 2`, because a one-site pattern is a symbol whose constant configuration it kills. Also `p_i` is
  nonconstant.
- Hence `eta_i <= -log(1 - 1/4) = log(4/3)` and `D_i >= |W_i| >= 2`, so `Sigma <= (n/2) log(4/3)`.
- On a surjunctive host `j' > j`, so `mu >= log 2`. Padding `D^(j')` into `D^j` would otherwise give an injective
  automaton from the full shift onto a proper subshift of it.
- So `mu < Sigma` needs `n > 2 log 2 / log(4/3) ≈ 4.82`, that is, at least 5 tracks.

**5.3 Where a construction must go.** A sub-threshold injection over `U`, with the image containing all constants,
has these properties:

- at least 5 tracks with nonconstant forbidden patterns;
- windows generating a nonsofic subgroup with finite `h_sup`, outside every sofic subgroup, and outside `V` unless
  `V` is nonsofic;
- the Rokhlin deficits it forces need `lambda(F)` and the read degree unbounded (2.1(c) and
  `self-copy-host-rokhlin-deficits-need-unbounded-windows`, item 3).

No candidate was built.

## 6. The missing inequality

1. **Positive side (V).** There are `q >= 2` and `c > 0` with `Phi(k, E, F, psi) >= c` for every configuration over
   `V` at `q`. This is recorded OPEN as `thompson-v-bernoulli-window-values-have-a-positive-floor`.
   - By Proposition 2.1 it is INF(V), and no smaller constant is weaker.
   - Its negation is one finite configuration over `V` with `Phi < log q`. Its pattern is decidable through the word
     problem of `U`, since `V <= U`.
   - It is implied by `thompson-v-is-sofic`.
   - It gives POS(V) (route `thompson-v-positive-rokhlin-from-window-floor`), then QS(V) by Corollary U, then
     surjunctivity of `V`.
2. **Negative side (U).** A sub-threshold injection as in Section 5 (`leavitt-units-are-not-quantitatively-surjunctive`),
   or directly one configuration over `U` with `Phi < log q` (`leavitt-units-have-zero-rokhlin-entropy-supremum`).
3. **Landed with this artifact.**
   - Claims `bernoulli-per-copy-rokhlin-entropy-is-zero-or-full` (Section 2) and
     `thompson-v-bernoulli-window-values-have-a-positive-floor` (Section 6.1), both held OPEN.
   - Route `thompson-v-positive-rokhlin-from-window-floor`.
   - Attempts on `leavitt-units-have-zero-rokhlin-entropy-supremum`, `leavitt-units-are-not-quantitatively-surjunctive`
     and `bernoulli-rokhlin-entropy-maximal-for-every-group`.
4. **Status.**
   - Proved on this lane's derivation, held open: Proposition 2.1, Remark 2.2, Propositions 3.1, 3.2, 5.1 and 5.2.
   - Refuted: none.
   - Open: the dichotomy on `U` and on `V`.
   - Next lead: a model-free floor on `Phi` over `V`, or a nonlinear sub-threshold injection over `U` on at least 5
     tracks.

Independent re-derivation of Sections 2, 3 and 5 is requested from w4-vf-positive-b.
