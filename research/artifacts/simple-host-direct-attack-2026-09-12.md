# Direct arguments on simple hosts: site pullbacks, centralized quotients, host manipulations

Lane `gk-p-simple-direct`, 2026-09-12. Supports the Cairn claims:

- `site-pullbacks-strict-iff-stabilizer-self-compressed`
- `surjectivity-descends-to-centralized-coset-quotients`
- `strict-automata-closed-under-host-manipulations`
- `surjunctivity-iff-automaton-monoid-directly-finite`
- `invariant-output-symmetry-must-be-core-free`

The question for this lane: can features that only simple nonsofic hosts have (no finite quotients,
compression and Hilbert-hotel structure, self-copies, simplicity) give an internal argument that an
injective automaton is onto? The answer recorded here is structural, and it narrows what such an
argument must contain.

1. Site-level Hilbert hotels never act strictly on free or finite-stabilizer shifts (Section 1).
2. Symmetry centralizing the memory only transfers strictness upward from central quotients of the
   memory group (Section 2).
3. Every manipulation the host supplies preserves strictness, so a contradiction needs a size that
   drops on proper retracts, which is direct finiteness of the automaton monoid (Section 3).
4. The one invariant-output filter these features give is core-freeness (Section 4).
5. Counting on the host itself is a Følner statement (Section 5).

Nothing here decides `fg-simple-kazhdan-groups-are-surjunctive` or `leavitt-unit-group-surjunctive`.

## 0. Conventions

- `G` is a group and `A` a finite alphabet with `|A| >= 2`. The shift is `(h.x)(g) = x(h^-1 g)`.
- A cellular automaton has a finite memory `M` containing `1` and a rule `mu`, with
  `tau(x)(g) = mu((x(gm))_(m in M))`.
- `R_c x(g) = x(gc)` is right translation. It is a bijective automaton with memory `{c}`.
- For a transitive left `G`-set `X = G/K`, the coset shift is `A^X` with `(h.y)(p) = y(h^-1 p)`.
- *Strict* means injective and not surjective.

## 1. Site pullbacks

**Theorem 1.** Let `X = G/K`.

- **(a)** The equivariant self-maps of `X` are `psi_c(gK) = gcK` for `c in G` with
  `c^-1 K c <= K`. Each is surjective, and `psi_c` is injective iff `c K c^-1 = K`.
- **(b)** A continuous equivariant `F: A^X -> A^X` whose value at each point reads a single site
  has the form `F(y) = theta o y o psi_c`, with `theta: A -> A` and `psi_c` as in (a), or is
  constant.
- **(c)** Such an `F` is injective iff `theta` is a bijection. Then `F` is strict iff `c^-1 K c` is
  a proper subgroup of `K`.
- **(d)** If `K` is finite, and in particular for the full shift (`K = 1`), every injective map of
  the form (b) is bijective.

*Proof.*

(a) `psi(K) = cK` for some `c`, and equivariance forces `psi(gK) = gcK`.
- **Well defined:** `gkcK = gcK` for all `k in K` iff `c^-1 k c in K` for all `k`.
- **Surjective:** `hK = psi_c(h c^-1 K)`.
- **Injective:** `psi_c(gK) = psi_c(g'K)` iff `g^-1 g' in c K c^-1`, so `psi_c` is injective iff
  `c K c^-1 <= K`. Together with `K <= c K c^-1` (well-definedness), that means equality.

(b) At the base point `o = K`, write `F(y)(o) = theta(y(p))` for the one site `p` it reads. If
`theta` is constant, `F` is constant by equivariance.
- For `k in K`: `F(k.y)(o) = F(y)(k^-1 o) = F(y)(o)`, and `(k.y)(p) = y(k^-1 p)`.
- If `theta` is nonconstant, take configurations that differ only at `k^-1 p`; this forces
  `k^-1 p = p`.
- So `K` fixes `p = cK`, meaning `K <= c K c^-1`, i.e. `c^-1 K c <= K`.
- Equivariance then gives `F(y)(gK) = theta(y(gcK))`.

(c) If `theta(a) = theta(a')` with `a != a'`, the constant configurations `a` and `a'` have the same
image. So assume `theta` is bijective and `F = theta o P_c` with `P_c y = y o psi_c`.
- `P_c` is injective because `psi_c` is onto.
- `P_c` is onto iff `psi_c` is injective: two points of one fibre of `psi_c` carry equal values in
  every image configuration.
- By (a), `F` is strict iff `c K c^-1 != K`, i.e. iff `c^-1 K c` is a proper subgroup of `K`.

(d) A finite group contains no proper conjugate of itself. QED

**Remarks.**
- **Scope:** the compressed-coset witness (`compressed-coset-shifts-carry-strict-equivariant-embeddings`,
  with `K = V_1` and `c = u^-1` over `R^x`) is the "if" half of (c). Theorem 1 adds the "only if"
  half. A Hilbert hotel on sites acts strictly exactly on a stabilizer properly conjugated into
  itself. It never acts strictly on the free regular action, or on a coset shift with finite
  stabilizers, which are the codomains of invariant-output designs.
- **Consequence:** a strict automaton on the full shift must read at least two sites essentially.
  Site-level compression is not available on free actions.
- **Link to unimodularity** (observation from lane `gk-p-bernoulli-mass`): the same computation runs
  for a locally compact group acting on a transitive space with compact open stabilizer `K`.
  - A proper self-conjugation `c^-1 K c < K` has finite index greater than 1, so the modular
    function satisfies `Delta(c) = [K : c^-1 K c] != 1` (up to the convention for `Delta`).
  - So compression of a compact open stabilizer is exactly a failure of unimodularity. This is
    where `end-fixing-tree-symmetries-carry-strict-automata` lives.
  - For a discrete group, stabilizers are compact only when finite, which is (d). The discrete
    witnesses need infinite stabilizers.

## 2. Centralized coset quotients

**Theorem 2.** Let `tau` be an automaton over `G` with memory `M` and rule `mu`, and let `B <= G`
satisfy `mb = bm` for all `m in M` and `b in B`. Put:

- `Y_B = {x : x(gb) = x(g) for all g in G, b in B}`,
- `Q = N_G(B)/B`,
- `Mbar = MB/B`.

Then:

- **(a)** `tau R_b = R_b tau` for `b in B`, and `tau(Y_B) <= Y_B`.
- **(b)** `Y_B = A^(G/B)`. The group `Q` acts freely on `G/B` from the right by `(gB)q = gqB`. On
  each right orbit `g N_G(B)/B`, the restriction of `tau` is the automaton `taubar` over `Q` with
  memory `Mbar` and rule `mubar(z) = mu((z(mB))_(m in M))`.
- **(c)** If `tau` is injective, `taubar` is injective. If `tau` is bijective, `taubar` is
  bijective.
- **(d)** If `tau` is injective and `taubar` is not surjective, then `tau` is strict. Over a
  surjunctive `G`, every injective automaton whose memory centralizes `B` has surjective quotient
  `taubar`.

*Proof.*

(a) `tau(R_b x)(g) = mu((x(gmb))_m) = mu((x(gbm))_m) = tau(x)(gb) = (R_b tau x)(g)`. If
`x = R_b x`, then `tau x = R_b tau x`.

(b) For `x in Y_B`, the value `tau(x)(gB) = mu((x(gmB))_m)` is well defined, because
`gbmB = gmbB = gmB`.
- For `q in N_G(B)`, `(gB)q` is well defined, and it equals `gB` only when `q in B`.
- On the orbit of `gB`, identify `qB` with `gqB`. Since `qm in N_G(B)`, the formula
  `tau(x)(gqB) = mu((x(gqmB))_m)` is the automaton over `Q` with memory `Mbar`.
- When two memory elements have the same image in `Q`, `mubar` reads that site twice.

(c) `tau` restricted to `Y_B` is the product, over orbits, of copies of `taubar`.
- Injectivity of `tau` passes to each factor.
- If `tau` is bijective and `y in Y_B`, its unique preimage `x` satisfies `tau(R_b x) = R_b y = y`.
  So `R_b x = x`, the restriction is onto `Y_B`, and every factor `taubar` is onto.

(d) follows from (c). QED

**Remarks.**
- **What matters:** only the effective memory group `Gamma = <M>`. On each coset, `taubar` is the
  automaton over `Gamma/(Gamma meet B)`, and `Gamma meet B` is central in `Gamma`. So Theorem 2
  says two things:
  - strictness ascends from a central quotient of the memory group to an injective lift;
  - surjectivity descends to the quotient.
- **Commuting copies give nothing new:** on `R^x` with `B = iota_1(U)` and memory in `iota_0(U)`,
  `Gamma meet B = 1` and `taubar` is `tau` again.
- **Where central quotients do enter:** through centres of memory groups, for example
  `G_3 = L_(F_3)(1,2)^x -> PG`.

## 3. Host manipulations and the automaton monoid

**Proposition 3.** Let `tau` and `rho` be injective automata over `G`, with `tau` strict.

- **(i)** For `c in G`, `tau^c := R_c tau R_(c^-1)`, the automaton with memory `c M c^-1` and rule
  `mu`, is strict.
- **(ii)** For an injective endomorphism `alpha` of `G`, the transported automaton `tau^alpha` with
  memory `alpha(M)` and rule `mu` is strict.
- **(iii)** `tau o rho` and `rho o tau` are strict.
- **(iv)** `tau x rho` over the alphabet `A x B` is strict.
- **(v)** For `H <= G` containing `M`, `tau` is strict iff its restriction to `H` is.

*Proof.*

- **(i)** Conjugate by the bijective automaton `R_c`: `R_c tau R_(c^-1)(x)(g) = mu((x(gcmc^-1))_m)`.
- **(v)** `tau` acts independently on the left `H`-cosets, and on each one it is the
  `H`-automaton.
- **(ii)** Apply (v) to `alpha(G)`, transported by the isomorphism `alpha: G -> alpha(G)`.
- **(iii)** Composites of injective maps are injective.
  - The image of `tau o rho` lies in `tau(A^G)`, which is proper.
  - The image of `rho o tau` is `rho(tau(A^G))`. It is proper when `rho` is onto, because `tau` is
    not onto; otherwise it lies in the proper set `rho(A^G)`.
- **(iv)** The image lies in `tau(A^G) x B^G`, which is proper. QED

**Proposition 3.1 (monoid form).** For a group `G` and an alphabet `A`, the following are
equivalent:
- `G` is `A`-surjunctive;
- the monoid `CA(G;A)` of automata is directly finite: `sigma tau = id` implies `tau sigma = id`.

*Proof.*
- **Forward:** if `G` is `A`-surjunctive and `sigma tau = id`, then `tau` is injective, hence
  bijective, and `sigma = tau^-1`.
- **Converse:**
  1. Let `tau` be injective, with image `X = tau(A^G)`.
  2. `tau^-1: X -> A^G` is continuous and equivariant. By uniform continuity at the identity and
     equivariance, there are a finite `N` and a function `nu` with
     `tau^-1(y)(g) = nu((y(gn))_(n in N))` for `y in X`.
  3. Extend `nu` arbitrarily to all of `A^N`. This gives an automaton `sigma` with
     `sigma tau = id`.
  4. Direct finiteness gives `tau sigma = id`, so `tau` is onto. QED

**Iterates.** Let `sigma tau = id`, with `tau` strict, and put `X_n = tau^n(A^G)`.
- **The chain is strictly decreasing:** if `X_(n+1) = X_n`, then
  `X_1 = sigma^n(X_(n+1)) = sigma^n(X_n) = A^G`, a contradiction.
- **Every term is conjugate to the full shift:** each `X_n` is conjugate to `A^G` by `tau^n`.
- **`tau` is bijective on the attractor `X_inf` (the intersection of the `X_n`):**
  - `tau(X_inf) <= X_inf`.
  - For `y in X_inf`, the preimage `sigma(y)` lies in every `X_(n-1)`.

**Consequences.**
- **An ideal:** strict automata form a two-sided ideal of the monoid of injective automata. It is
  closed under host conjugation, transport along injective endomorphisms, and products.
- **On `R^x`:** the commuting copies `iota_0(g) = s0 g t0 + s1 t1` and `iota_1(g) = s0 t0 + s1 g t1`
  transport a strict `tau` to commuting strict automata `tau_0` and `tau_1`. So does the doubling
  `g -> s0 g t0 + s1 g t1`.
  - Their composite is strict and misses two independent patterns.
  - Units supported on disjoint cylinders commute, so iterating gives strict automata that miss any
    finite number of independent patterns.
- **What a proof must supply:** none of these operations turns a strict automaton into a bijective
  one, so they cannot yield a contradiction by themselves. A proof on a simple host has to supply a
  size on `CA(G;A)` that drops strictly on every proper retract `E = tau sigma != id`. Proposition
  3.1 says that is exactly direct finiteness. The known sizes:
  - sofic counting, for sofic `G`;
  - Rokhlin entropy (`strict-automaton-lowers-bernoulli-rokhlin-entropy`), given a lower bound on
    Bernoulli Rokhlin entropy;
  - none yet on a nonsofic host.

## 4. Invariant-output symmetry must be core-free

**Proposition 4.** Let `tau` be an injective automaton over `G` with `tau(x)(gh) = tau(x)(g)` for
all `x`, all `g`, and all `h in H <= G`.
- `H` contains no nontrivial normal subgroup of `G`.
- If the memory `M` generates `Gamma` and `H <= Gamma`, then `H` contains no nontrivial normal
  subgroup of `Gamma`.

*Proof.*
1. Let `N <= H` be normal in `G`, and `n in N`.
2. For every `g`, `ng = g(g^-1 n g)` with `g^-1 n g in H`. So `tau(x)(ng) = tau(x)(g)`, that is,
   `tau(n^-1 . x) = tau(x)`.
3. Injectivity gives `n^-1 . x = x` for all `x`. The shift is free, so `n = 1`.
4. For `Gamma`: restrict `tau` to `Gamma` (Proposition 3(v)). There the invariance holds for
   `g in Gamma`, and the same argument runs inside `Gamma`. QED

**Remark.** On an infinite simple memory group this is vacuous. It is a genuine filter for design
lanes whenever the effective memory group has normal subgroups meeting the candidate symmetry. In
particular a symmetry central in the memory group is impossible.

## 5. Counting on the host

Let `tau` be strict with a Garden-of-Eden pattern on `Omega`. Let `X` be the image, `N` the memory
of a left inverse, and `F` finite. Put `F' = {g : gM <= F}` and `F'' = {g : gN <= F'}`.
- **Lower bound:** the left inverse recovers `x` on `F''` from `tau(x)` on `F'`. So
  `|A|^|F''| <= |L_(F')(X)|`.
- **Upper bound:** take a maximal family `E <= F'` of centres of pairwise disjoint translates
  `g Omega <= F'`. It satisfies `|E| >= |{g : g Omega <= F'}| / |Omega Omega^-1|`, and
  `|L_(F')(X)| <= (1 - |A|^-|Omega|)^|E| |A|^|F'|`.
- **The gap:** a contradiction needs `|F'| - |F''|` to be small against `|E|`, i.e. Følner sets.
  On a nonamenable host both boundary terms are a positive fraction of `|F'|`.
- **Two-cell windows:** for `Omega = {1, h}` with `h` of infinite order, nothing changes.

So counting along the host itself is an amenability statement. Without finite models it gives
nothing on a simple nonsofic host.

## 6. What a direct argument on a simple host must supply

1. **Freeness with essential two-site reading.** Theorem 1 excludes site-level compression. The
   compressed coset shifts are exactly the self-compressed-stabilizer case.
2. **A size on the automaton monoid that drops on proper retracts.** Proposition 3.1 identifies
   this with the goal, and Proposition 3 shows the host's own manipulations never supply it.
3. **Central quotients help only upward.** Theorem 2: they transfer strictness from a quotient to a
   lift, and surjectivity from a lift down to the quotient.
4. **Counting is a Følner statement** (Section 5).
