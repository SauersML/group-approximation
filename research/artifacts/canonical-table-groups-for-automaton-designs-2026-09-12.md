# Canonical table groups for automaton designs

Lane `gk-design-group`, 2026-09-12. Handwritten proofs; nothing was run.
Supports `strict-automata-live-on-canonical-table-groups` and
`triangular-forward-tables-force-surjectivity`.

The starting question was "choose the group last": fix the finite data of an
injective non-surjective automaton, then find a group realizing it. Section 2
shows that no choice is left. Once the rule pair and a minimal forward
partition are fixed, one finitely presented group is the only one that matters.

## 0. Conventions

`G` is a group and `A` a finite alphabet with `|A| >= 2`. A cellular automaton
with memory list `(g_m)_(m in M)` and rule `mu : A^M -> A` computes

```text
tau(x)(g) = mu( (x(g g_m))_(m in M) ).
```

A **design** `D = (A, S, M, nu, mu)` is purely finite: finite index sets `S`, `M`
of formal addresses with distinguished identity addresses `1_S`, `1_M`, and rules
`nu : A^S -> A`, `mu : A^M -> A`. A **realization** of `D` in `G` is a map
`rho : S ⊔ M -> G` with `rho(1_S) = rho(1_M) = 1`. It defines `tau_rho` (memory
`rho(M)`, rule `mu`) and `sigma_rho` (memory `rho(S)`, rule `nu`). Addresses may
collide under `rho`, and unread addresses are allowed.

A **marked partition** of a finite set `X` with base point `b` is a partition
together with a marked class `e` containing `b`. Write `P <= P'` when every
class of `P` lies in a class of `P'` and `e(P) ⊆ e(P')`.

The **forward table** of `rho` is the marked partition `E_rho` of `S x M` with
base point `(1_S,1_M)`: `(s,m) ~ (s',m')` iff `rho(s)rho(m) = rho(s')rho(m')`, and
`e = {(s,m) : rho(s)rho(m) = 1}`. The **reverse table** `F_rho` is the marked
partition of `M x S` defined the same way from the products `rho(m)rho(s)`.

For a marked partition `E` of `S x M` and `y` assigning one symbol to each class,
put

```text
Phi_E(y) = nu( ( mu( (y[(s,m)])_(m in M) ) )_(s in S) ).
```

`E` is **forward sufficient** for `D` if `Phi_E(y) = y[e(E)]` for every `y`. For a
marked partition `F` of `M x S` put `Psi_F(y) = mu( ( nu( (y[(m,s)])_(s in S) ) )_(m in M) )`
and call `F` **reverse sufficient** if `Psi_F(y) = y[e(F)]` for every `y`.
Write `𝓕_D` and `𝓡_D` for these two families.

## 1. The finite data

**Lemma 1 (composites read the tables).** `sigma_rho tau_rho = id` iff `E_rho` is
in `𝓕_D`, and `tau_rho sigma_rho = id` iff `F_rho` is in `𝓡_D`.

*Proof.* `sigma_rho(tau_rho x)(g) = nu( (mu( (x(g rho(s) rho(m)))_m ))_s )`. The
points `g rho(s) rho(m)` coincide exactly according to `E_rho`, and the class
`e(E_rho)` is the point `g`. Every assignment of symbols to these distinct points
extends to a configuration. So the composite is the identity at `g` for all `x`
iff `Phi_(E_rho)` is the projection to the marked class. Left translation moves
`g` to every site. The reverse statement is the same computation on `M x S`. QED

**Lemma 2 (coarsening).** If `E <= E'` and `E` is in `𝓕_D`, then `E'` is in `𝓕_D`.
The same holds for `𝓡_D`.

*Proof.* The quotient `q` from the classes of `E` to those of `E'` sends `e(E)`
into `e(E')`. For `y'` on the classes of `E'` put `y = y' o q`. Then
`Phi_(E')(y') = Phi_E(y) = y[e(E)] = y'[e(E')]`. QED

So `𝓕_D` and `𝓡_D` are up-sets in finite lattices, determined by `(nu, mu)` alone.
Their minimal elements `𝓕_min` and `𝓡_min` are finite and computable.

**Lemma 3 (strictness).** Let `E_rho` be in `𝓕_D`. Then `tau_rho` is injective, and
it is surjective iff `F_rho` is in `𝓡_D`.

*Proof.* `sigma_rho` is a left inverse. If `tau_rho` is surjective it is bijective,
so `sigma_rho = tau_rho^-1` and `tau_rho sigma_rho = id`. Conversely
`tau_rho sigma_rho = id` gives surjectivity. Apply Lemma 1. QED

**Lemma 4 (left inverses exist).** Every injective automaton `tau` over any group
has an automaton `sigma` with `sigma tau = id`.

*Proof.* `tau` is a continuous injection of the compact space `A^G`, hence a
homeomorphism onto its closed image `X`. The map `x -> tau^-1(x)(1)` is continuous
on the compact `X`, so it depends on a finite window. Extend that local rule
arbitrarily to all patterns on the window. Equivariance gives `sigma tau = id`. QED

So every injective automaton is a realization of a design with `E_rho` in `𝓕_D`.

## 2. The canonical group

For a marked partition `E` of `S x M` let

```text
U_E = < x_a  (a in S ⊔ M minus {1_S, 1_M})  |
        x_s x_m = x_s' x_m'   for (s,m) ~_E (s',m'),
        x_s x_m = 1           for (s,m) in e(E) >,
```

with `x_(1_S)` and `x_(1_M)` the empty word. It suffices to impose one relator per
edge of a spanning tree of each class, which gives `|S x M| - #classes(E)` relators
of length at most four. Letters are indexed by formal addresses, so an address in
`S` and one in `M` are different letters even when a realization maps them to the
same element. Put `rho_E(a) = x_a`.

**Lemma 5 (universality).** `E_(rho_E) >= E`. If `rho` realizes `D` in `G` with
`E_rho >= E`, then `x_a -> rho(a)` defines a homomorphism `pi : U_E -> G`, and
`F_rho >= F_(rho_E)`.

*Proof.* The first claim is the relators. The relators hold in `G` because
`E_rho >= E`, so `pi` exists. `pi` maps `x_m x_s` to `rho(m)rho(s)`, so equal
reverse products and products equal to `1` stay equal. QED

**Theorem A (canonical group).** For a design `D` the following are equivalent.

1. Some realization of `D` in some group has `sigma tau = id` and `tau` not surjective.
2. Some realization has forward table in `𝓕_D` and reverse table outside `𝓡_D`.
3. Some minimal `E` in `𝓕_D` has `F_(rho_E)` outside `𝓡_D`. Then the realization
   over `U_E` is injective and not surjective.

*Proof.* (1) and (2) are equivalent by Lemmas 1 and 3.
(2) implies (3): choose `E` minimal in `𝓕_D` with `E <= E_rho`. By Lemma 5,
`F_rho >= F_(rho_E)`. If `F_(rho_E)` were in `𝓡_D`, Lemma 2 would put `F_rho` in
`𝓡_D`. Also `E_(rho_E) >= E` is in `𝓕_D`. Lemma 3 applies over `U_E`.
(3) implies (1) with the group `U_E`. QED

**Corollary B.** Gottschalk's conjecture holds iff, for every design `D` and every
minimal `E` in `𝓕_D`, the reverse table of `U_E` is reverse sufficient.

*Proof.* Lemma 4 turns a counterexample over any group into (1) for some design. QED

**Reading.** Choosing the group last leaves no freedom. Amalgamating, adding
relations, adjoining a Kazhdan subgroup, or passing to any other group realizing `E`
only coarsens the reverse table (Lemma 5), and coarsening can only help surjectivity
(Lemma 2). Padding a design with unread addresses adds free letters and nothing
else, because a minimal forward partition never identifies a pair that the rules do
not need. So every group-theoretic structure a counterexample uses must be forced by
the minimal forward sufficiency of the rule pair itself. The negative search is a
search over finite rule pairs, and then one explicit presentation per minimal forward
partition.

`forward-memory-lifts-exclude-strict-cellular-sections` gives the presentation
attached to a given pair in a given group. Theorem A makes it intrinsic to the rule
pair, and adds the equivalence.

## 3. Hinge words and sofic quotients

For a marked partition `F` of `M x S` choose a spanning tree of every class, and let
`W(F)` be the set of words `x_s'^-1 x_m'^-1 x_m x_s` over the tree edges, together
with `x_m x_s` for the tree edges of the marked class. A realization has
`F_rho >= F` iff every word of `W(F)` maps to `1`.

**Proposition C (hinge form).** Let `E` be minimal in `𝓕_D`. The realization over
`U_E` is strict iff for every `F` in `𝓡_min` some word of `W(F)` is nontrivial in
`U_E`. For each sofic quotient `Q` of `U_E`, some `F` in `𝓡_min` has all of `W(F)`
in `ker(U_E -> Q)`.

*Proof.* The first sentence is Theorem A with the up-set `𝓡_D` generated by `𝓡_min`.
For the second, the realization over `Q` has forward table `>= E`, so it is
injective. Sofic groups are surjunctive (Gromov--Weiss; recovered in
`sofic-radical-localizes-garden-of-eden-windows`), so its reverse table lies in
`𝓡_D` and dominates some `F` in `𝓡_min`. QED

So a strict design needs, for every minimal reverse hinge, a word that survives in
`U_E`, while every sofic quotient kills an entire hinge. This complements Theorem F of
`gottschalk-sofic-radical-localization-2026-09-11.md`, which places one invisible
difference inside a Garden-of-Eden window.

## 4. Triangular forward partitions

Write each relator of `U_E` as a freely reduced word. Call `E` **triangular** if its
spanning-tree relators can be ordered `r_1, ..., r_k`, with distinct letters
`x_1, ..., x_k`, such that `x_i` occurs exactly once in `r_i` and does not occur in
`r_j` for `j > i`.

**Lemma 6.** If `E` is triangular, `U_E` is free on the letters other than
`x_1, ..., x_k`.

*Proof.* Eliminate `x_k` using `r_k`: it occurs once there, so `r_k` expresses `x_k`
as a word in other letters. Substitute into `r_1, ..., r_(k-1)` and delete `r_k` and
`x_k`. That word contains no `x_i` with `i < k`, because those letters do not occur in
`r_k`. So each `x_i` still occurs exactly once in `r_i` and in no later relator.
Induct downward. The last step leaves no relators. QED

**Theorem D.** Let `E` in `𝓕_D` be triangular. Over every group `G` and every
realization `rho` with `E_rho >= E`, `tau_rho` is bijective.

*Proof.* `U_E` is free (Lemma 6), hence residually finite and surjunctive
(`residually-finite-groups-are-surjunctive`). Over `U_E` the forward table dominates
`E`, so `tau` is injective, hence surjective, and `F_(rho_E)` is in `𝓡_D` (Lemma 3).
By Lemma 5, `F_rho >= F_(rho_E)`, so `F_rho` is in `𝓡_D` by Lemma 2. Lemma 3 gives
bijectivity over `G`. QED

**Examples.**

- A collision-free rectangle has no relators. This recovers Section 3 of
  `gottschalk-nonlinear-ca-search-2026-08-24.md`.
- A single relator is always triangular. With formal letters its four positions carry
  distinct letters unless `s = s'` or `m = m'`, and then the relator reduces to
  `x_m = x_m'` or `x_s = x_s'`. So **every forward partition with at most one
  relator is triangular**, and a strict design needs at least two relators that
  cannot be eliminated.
- More generally, the letters of a non-triangular core all occur in at least two
  relators after every possible elimination. By Theorem A and Theorem F that core
  presents a nonsofic group with relators coming only from coincidences the rules
  need.

## 5. Where the constructions die

- **Hilbert hotel with one address.** "Copy the parent, decode from child 0" is the
  design `M = {1, p}`, `S = {1, c}`, `mu` reading `p` and `nu` reading `c`. Its
  minimal forward partition has the single relator `x_c x_p = 1`, which is triangular.
  In a group a one-sided inverse is two-sided: `x_p x_c = 1` follows, so the reverse
  table is sufficient. The monoid version (bicyclic `qp = 1 != pq`) has no analogue.
- **Cyclic linear units.** Over `C_7`, `a = 1 + g + g^2` has inverse
  `b = 1 + g^2 + g^3 + g^5 + g^6` in `F_2[C_7]`. The forward parity partition,
  refined minimally (base class `{(1,1)}` plus six pairs), gives relators that
  eliminate to `t^7 = 1` for `t = x_g`. So the table group is `C_7` and the reverse
  identity holds. Dense forward tables force commutation.
- **Padding by structure.** Adjoining a compression configuration through unread
  addresses changes nothing (Section 2, Reading). The configuration has to be forced
  by what the decoder needs.

Open target, recorded in Cairn through `strict-automata-live-on-canonical-table-groups`:
a rule pair whose minimal forward partition has a non-triangular core in which every
reverse hinge keeps a nontrivial word. Such a core presents a nonsofic group, and the
rule pair must force it.
