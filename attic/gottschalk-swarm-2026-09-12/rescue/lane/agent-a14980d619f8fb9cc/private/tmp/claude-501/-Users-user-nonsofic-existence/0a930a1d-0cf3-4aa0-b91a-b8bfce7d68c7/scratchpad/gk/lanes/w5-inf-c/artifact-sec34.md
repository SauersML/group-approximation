
## 3. On self-copy hosts a deficit forces total collapse with unbounded windows

**Theorem 3.1.** Let `G` be countably infinite with `h^Rok_sup(G) ∈ {0, ∞}`. This holds when `G`
contains `G × G` and finite subgroups of unbounded order
(`rokhlin-supremum-dichotomy-with-centralized-self-copies`), for instance the binary Leavitt unit
group and Thompson's `V`. Suppose some configuration over `G` has `Phi < log q` for some `q`. Then:
1. `h^Rok_sup(G) = 0`, and every uniform Bernoulli shift over `G` has Rokhlin entropy `0`;
2. for every `q' >= 2` and every `ε > 0` some configuration at `q'` has `Phi < ε`;
3. every configuration with `Phi < log q' / m` has `|E| > m` and `H(psi)/k < log q'/m`.

*Proof.*
1. By `bernoulli-rokhlin-deficit-has-a-finitary-witness`, `rho_q(G) = inf Phi < log q`, so some `k`
   has `h^Rok_G((A^k)^G) < k log q`. By item 1 of
   `seward-per-group-rokhlin-entropy-of-bernoulli-shifts` that value is `min{k log q, h_sup(G)}`,
   so `h_sup(G) < ∞`, hence `h_sup(G) = 0`, and `min{H(L), 0} = 0` for every finite base.
2. Then `rho_(q')(G) = lim_k h^Rok((A'^k)^G)/k = 0 = inf Phi` at `q'`.
3. Theorem 2.1. QED.

**Corollary 3.2 (counterexample filter).** By `leavitt-zero-rokhlin-supremum-from-strict-automaton`,
a strict automaton over `U = L_(F_2)(1,2)^x` forces conclusions 1–3 on `U`. In particular `U` then
carries, at every alphabet, configurations of arbitrarily small value whose windows are arbitrarily
large, and by Theorem 1.1 every such window has a non-Rokhlin-maximal difference subgroup.

## 4. Mechanism audit for a model-free lower bound

The directive listed three candidate mechanisms. Each is covered below by a landed barrier or
reduces to a landed normal form. Literature items not read locally are flagged.

### 4.1 Cost and ℓ²-type invariants

`weak-invariants-give-no-bernoulli-rokhlin-lower-bound` (via
`nontrivial-bernoulli-shifts-are-weakly-equivalent` and `cost-is-constant-on-weak-equivalence-classes`)
shows that any lower bound computed from a weak-equivalence invariant is non-positive on Bernoulli
shifts: the bound is the same for bases of vanishing entropy, whose Rokhlin entropy is at most
their base entropy. That kills positive bounds too, so the dichotomy of Section 3 does not revive
these invariants. ℓ²-Betti numbers of the orbit relation of a free action equal those of the group
(Gaboriau; not re-read locally), so they are constant over all free actions and fall under the
same argument. On the reduction hosts property (T) makes the first one vanish anyway.

### 4.2 Ergodic decomposition and spectral data

Bernoulli shifts are ergodic, so an ergodic decomposition formula for Rokhlin entropy (Seward; not
re-read locally) is trivial on them. The spectral data that strong ergodicity or a spectral gap
supplies are properties of the Koopman representation on `L²_0`. For every nontrivial base it
decomposes into quasi-regular representations over finite subsets of `G`, independently of the
base (standard; not re-read locally). A bound `h^Rok(L^G) >= F(spectral data)` is then the same for
bases of entropy tending to `0`, so `F <= 0`, as in 4.1.

### 4.3 Subgroups, co-amenability, co-induction

- `simple-kazhdan-groups-have-no-proper-co-amenable-subgroups`: on the canonical hosts the only
  co-amenable subgroup is the group itself, so Følner-type induction from a subgroup returns INF
  unchanged (artifact `rokhlin-lower-bounds-without-finite-models-2026-09-12.md`, §1.2).
- Restriction to a subgroup, and co-induction from one, give upper bounds only
  (`rokhlin-entropy-self-copy-dichotomy-2026-09-12.md`, §4).
- The co-induced Bernoulli shift is Bernoulli: `CoInd_H^G(L^H) = L^G`. So a lower bound
  `h^Rok_G(CoInd_H^G Y) >= h^Rok_H(Y)` for Bernoulli `Y` over an infinite sofic `H <= G` says
  exactly `h^Rok_G(L^G) = H(L)` for every finite base, which is RBS(`G`). This mechanism is the
  normal form itself.
- Theorem 1.1 is the one subgroup reduction that runs the useful way. It moves a witness into
  `<E E^-1>`, a statement about configurations, not an induced lower bound.

### 4.4 Normal form and the smallest open case

- **The normal form.** On self-copy hosts, INF(`G`) is equivalent to positivity of the binary
  Bernoulli shift's Rokhlin entropy (`leavitt-unit-group-has-positive-rokhlin-entropy-action` for
  `U`). By `bernoulli-rokhlin-deficit-has-a-finitary-witness` together with Theorem 3.1, it is one
  uniform statement: some `c > 0` bounds `Phi` below over all binary configurations on `U`, and
  then the dichotomy upgrades `c` to `log 2`.
- **What has to be beaten.** A proof only has to handle configurations with `|E| → ∞` and
  `H(psi) → 0` (Theorem 3.1), whose difference subgroups are infinite and not Rokhlin-maximal
  (Theorem 1.1).
- **The smallest open case is uniformity, not a small window.** Windows of size at most 2 never
  witness, and at every fixed read degree `m` Theorem 2.1 already gives `Phi >= log q/m`. What is
  open is a bound uniform in `m`.
- **The missing input.** It is an averaging over codewords that goes beyond subadditivity, the
  Rokhlin-level counterpart of `injective-ca-random-order-transport-is-dominated` (transport
  domination for injective automata). The only known way to get such an averaging is counting on
  finite models (Gromov–Weiss, sofic entropy). INF implies the injective-automaton normal forms
  (`injective-ca-images-have-full-single-site-entropy`), and no converse is known.

## 5. Where it stops

- No lower bound for Rokhlin entropy of any nonsofic group is proved here.
- Theorems 1.1, 2.1 and 3.1 are filters on witnesses. They show where a deficit must live (a
  non-maximal difference subgroup, unbounded windows, total collapse on self-copy hosts). They
  decide neither INF nor POS on any nonsofic host.
