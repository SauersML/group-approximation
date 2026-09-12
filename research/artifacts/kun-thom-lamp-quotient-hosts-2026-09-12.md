# Lamp quotients of the Kun--Thom coset wreath as Gottschalk hosts

Lane `w4-free-neg-b`, 2026-09-12. Handwritten proofs; nothing was run. Supports
`kun-thom-wreath-lamp-quotient-nonsurjunctive`,
`kun-thom-lamp-quotients-have-lamp-sofic-radical`,
`residually-permutational-lamp-extensions-are-surjunctive` and
`strict-lamp-quotient-realizations-need-lamp-hinges`.

## 0. Why quotients

`surjunctivity-passes-to-quotients` is equivalent to the goal. The Kun--Thom coset wreath `W` is
surjunctive and not sofic, and its whole failure of soficity sits in one elementary abelian
2-group of lamps, `K_even` (`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`). Quotienting
`W` by a lamp submodule inside `K_even` keeps the quotient nonsofic, but destroys the lamp sites
that the surjunctivity proof peels. So these quotients are where a sofic radical could become a
surjunctive radical.

The family differs from the other Kun--Thom hosts:
- the Clifford cover (`kun-thom-clifford-cover-nonsurjunctive`) is a central extension of `W`,
  not a quotient;
- the intermediate coset wreaths `W_K` (`kt-intermediate-coset-wreaths-are-nonsofic`) are
  quotients by permutation kernels, and they are surjunctive (Section 3).

## 1. Setting

`Gamma < G` is the Theorem E pair of `kun-thom-nonsofic-wreath`, `N = EL_r(R)` the normal closure
of `Gamma`, and `G = EL_r(R) x| SL_d(Z)` is residually finite. Write the lamp group additively,

    P = direct_sum_(G/Gamma) Z/2 = F_2[G/Gamma],   basis e_x,      W = P x| G.

`pi : G/Gamma -> G/N` is the fibre map and `K_even <= P` the configurations meeting every fibre
of `pi` evenly. For a `G`-submodule `U <= P` put

    V_U = P / U,        H_U = W / U = V_U x| G.

**Example.** For `Gamma <= K <= G` let `U_K` be the kernel of `P -> F_2[G/K]`, `e_(g Gamma) -> e_(gK)`,
that is, the configurations even on every fibre of `G/Gamma -> G/K`. Then `H_(U_K) = W_K`. When
`K <= N`, every `N`-fibre is a union of `K`-fibres, so `U_K <= K_even`, and `U_N = K_even`.

## 2. The sofic radical of a lamp quotient

`Rad_sof(H)` is the intersection of the kernels of all homomorphisms from `H` to sofic groups.

**Theorem A.** For every `G`-submodule `U <= K_even`, `Rad_sof(H_U) = K_even / U`. So `H_U` is
nonsofic iff `U != K_even`.

*Proof.* Let `q : W -> H_U` be the quotient and `psi : H_U -> S` a homomorphism into a sofic
group. Then `psi o q` kills `Rad_sof(W) = K_even`, so `psi` kills `q(K_even) = K_even/U`.
Conversely `H_U / (K_even/U) = W / K_even = W_N`, which is residually finite by part 2 of the
radical theorem, hence sofic. So `K_even/U` is itself the kernel of a homomorphism into a sofic
group. QED

## 3. Residually permutational lamp extensions

Let `Q` be a group and `V` an abelian group with a `Q`-action, `E = V x| Q`. Call `V`
**residually permutational** if for every `v != 0` in `V` there are a `Q`-set `Y`, a residually
finite group `A`, and a `Q`-equivariant homomorphism `phi : V -> direct_sum_Y A` with
`phi(v) != 0`. Here `Q` permutes the sites of `Y` and acts trivially on `A`.

**Theorem B.** If `Q` is surjunctive and `V` is residually permutational, then `E = V x| Q` is
surjunctive.

*Proof.* Suppose `(tau, sigma, p)` is a strict pair over `E` with window `Omega` and
`F = {1} ∪ M ∪ S ∪ Omega ∪ SM ∪ Omega M` as in `strict-pairs-transfer-to-table-realizations`.
Write elements of `E` as `(v, g)`. For each pair `w != w'` in `Omega` with `p(w) != p(w')` and
the same `Q`-part, choose `(Y_i, A_i, phi_i)` with `phi_i(v_w - v_w') != 0`. Finitely many
indices `i in I` suffice. Put `Y = disjoint_union_i Y_i` with the diagonal `Q`-action,
`A = prod_(i in I) A_i` (residually finite), and let `phi = sum_i phi_i : V -> direct_sum_Y A`,
placing `A_i` as the `i`-th factor at the sites of `Y_i`. It is `Q`-equivariant, so

    psi : E -> A wr_Y Q,        psi(v, g) = (phi(v), g)

is a homomorphism: `(v,g)(v',g') = (v + g v', g g')` goes to `(phi(v) + g phi(v'), g g')`.
`psi` respects every product in `F`, and `psi(w) = psi(w')` would need equal `Q`-parts and
`phi(v_w - v_w') = 0`, which the choice excludes. By the transfer theorem `A wr_Y Q` carries a
strict pair. It is a permutational wreath product with residually finite lamps over the
surjunctive group `Q`, so it is surjunctive (`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`).
Contradiction. QED

**Lemma 3.1 (binary targets).** If `V` is an elementary abelian 2-group, it is residually
permutational iff for every `v != 0` some `Q`-map `phi : V -> F_2[Y]` has `phi(v) != 0`.

*Proof.* The image of `V` in `direct_sum_Y A` lies in `direct_sum_Y A[2]`, and `A[2]` is an
`F_2`-vector space. Choose a linear functional `lambda` on `A[2]` that is nonzero on one nonzero
coordinate of `phi(v)` and apply it at every site. This is `Q`-equivariant because `Q` acts
trivially on `A`. QED

**Lemma 3.2 (Frobenius).** `Hom_G(P, F_2[Y]) = F_2[Y]^Gamma`: a map is `phi_c(e_(g Gamma)) = g c`
for a finitely supported `Gamma`-fixed vector `c`, that is, a finite sum of indicators of finite
`Gamma`-orbits in `Y`. This is Frobenius reciprocity for `P = Ind_Gamma^G F_2`.

For a submodule `U <= P` define its **permutation closure**

    U-bar = intersection of ker(phi_c) over all Y and all c in F_2[Y]^Gamma with phi_c(U) = 0.

`U` is **closed** if `U-bar = U`. By Lemmas 3.1--3.2, `V_U` is residually permutational iff `U`
is closed.

**Corollary 3.3.** For every closed `U <= K_even`, `H_U` is surjunctive, since `G` is residually
finite. The closed submodules include `0`, every `U_K` with `Gamma <= K <= N` (take `Y = G/K`,
`c = e_K`), and every intersection of kernels of maps `phi_c`. So:
- every intermediate coset wreath `W_K` with `Gamma <= K <= N` is surjunctive, and nonsofic when
  `K != N`;
- a Gottschalk counterexample among the lamp quotients needs a non-closed `U`.

**Example 3.4 (pair submodules are closed).** For `n in N` let `U_n` be the submodule generated
by `e_Gamma + e_(n Gamma)`, and `L = <Gamma, n>`.
- A map `phi_c` kills `U_n` iff `n c = c`, that is, iff `c` is `L`-fixed. Then `phi_c` factors
  through `P -> F_2[G/L]`, so `U-bar_n = U_L`.
- `U_n` is spanned by the edge configurations `e_(g Gamma) + e_(g n Gamma)`. The components of
  that edge graph are the `L`-fibres. An even configuration on a component is a sum of edges
  along paths, so `U_n = U_L`.

So submodules generated by one fibre pair give only intermediate coset wreaths. A candidate needs
generators of weight at least four whose relations no permutation image sees.

## 4. What a strict realization over a lamp quotient must use

Notation of `strict-automata-live-on-canonical-table-groups`: a design `D = (A, S, M, nu, mu)`, a
realization `rho`, the forward table `E_rho`, the reverse table `F_rho`, and the up-sets
`𝓕_D` and `𝓡_D`.

**Theorem D.** Let `U <= P` be any submodule and `rho` a realization of `D` over `H_U` with
`E_rho` in `𝓕_D` and `F_rho` not in `𝓡_D`, so `tau_rho` is strict. Let `rho~` be any lift of
`rho` to `W` with `rho~(1) = 1`. Then `E_(rho~)` is not in `𝓕_D`. So some cell pair identified,
or some cell marked, by `E_rho` has hinge word

    h = (rho~(s') rho~(m'))^-1 rho~(s) rho~(m)        (or rho~(s) rho~(m) for a marked cell)

that is a nonzero element of `U`. When `U <= K_even` this hinge is a fibre-even lamp configuration
with trivial `G`-part.

*Proof.* The quotient `q : W -> H_U` is a homomorphism with `q o rho~ = rho`, so equal products
stay equal and `E_(rho~) <= E_rho`, `F_(rho~) <= F_rho`. If `E_(rho~)` were in `𝓕_D`, `tau_(rho~)`
would be injective over `W` (Lemma 3 there). `W` is surjunctive
(`kun-thom-nonsofic-wreaths-are-surjunctive`), so `tau_(rho~)` would be bijective and `F_(rho~)`
in `𝓡_D`. By coarsening (Lemma 2 there), `F_rho` would be in `𝓡_D`, and `tau_rho` surjective.
Contradiction. Since `E_rho` is in `𝓕_D` and `E_(rho~)` is not, they differ. A coincidence of
`E_rho` missing from `E_(rho~)` has a hinge word that is nontrivial in `W` and trivial in `H_U`,
hence a nonzero element of `U`. QED

So a strict design over `H_U` reads a nonzero lamp relation of `U` among its forward
coincidences. Because `U <= K_even = Rad_sof(W)`, each such hinge is invisible in every sofic
image of `W`, and it meets some `N`-fibre of `G/Gamma` in at least two cosets.
