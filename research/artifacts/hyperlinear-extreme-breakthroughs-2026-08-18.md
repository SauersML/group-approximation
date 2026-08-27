# Extreme Q3.4 proof-development integration

**Date:** 2026-08-18  
**Integrated against GitHub `main`:** `ad7c8d8294a0c8c19c044ba93c1b5688f931bc43`  
**Question:** Must every hyperlinear group be sofic?  
**Status:** **OPEN. No complete proof or counterexample is claimed here.**

This is the canonical Cairn artifact for the second creative proof-development sprint on Pestov Question 3.4. It integrates the proved reductions, the corrected versions of the first divergent strategies, the failed routes, and the surviving theorem targets into the current graph. The earlier source sprint was performed against an uploaded snapshot older than current GitHub `main`; current `main` had already ingested the first divergent-strategies dossier, the exact projective-kernel/character Diracization program, and the positive-loss/uniform-gap reformulations. Those are therefore used as existing infrastructure rather than duplicated.

The central new spine is

```text
regular hyperlinear finite table
        |
        v
regular-character-markovization          [OPEN]
        |
        v
markov-sofic-equals-sofic                [PROVED]
        |
        v
permutation / sofic finite table
```

The main conceptual conclusion is that **Birkhoff integrality is not the hard part**. Once phase/interference has been erased into a genuinely multiplicative family of doubly stochastic kernels that also respects inverse relations, the kernels are automatically close to permutations with dimension-free control. The hard gate is therefore **whole-table Markovization**.

---

## 1. Proved: approximate inverse forces a Birkhoff extreme point

Let `B_N` be the Birkhoff polytope and use normalized Frobenius norm

```text
||A||_{2,N}^2 = (1/N) sum_{i,j}|a_ij|^2.
```

If `P,Q in B_N` and

```text
||PQ-I||_{2,N} <= eps,
```

then there is a permutation matrix `S` with

```text
||P-S||_{2,N}^2 <= 1-(1-eps)^2 <= 2 eps.
```

The same holds for `Q`. The proof is elementary. Doubly stochastic matrices are convex combinations of permutations and have operator norm at most one, so

```text
1-eps <= ||PQ||_{2,N} <= ||P||_{2,N},
1-eps <= ||PQ||_{2,N} <= ||Q||_{2,N}.
```

If `P=sum lambda_a S_a` is a Birkhoff decomposition, then

```text
||P||_2^2 = sum lambda_a <P,S_a>,
```

so some `S_a` satisfies `<P,S_a> >= ||P||_2^2`; expanding `||P-S_a||_2^2` gives the bound. This is `birkhoff-approx-inverse-permutation`.

### Consequence: Markov-soficity is exactly soficity

Suppose a finite group table has doubly stochastic matrices `P_g` with small normalized-Frobenius product defect, `P_e` near `I`, and trace near zero on tested nonidentity elements. Inverse relations make `P_gP_{g^{-1}}` near `I`, so the theorem rounds each `P_g` to a permutation `S_g` with `||P_g-S_g||_2=o(1)`. Since every doubly stochastic matrix has operator norm at most one,

```text
||S_gS_h-S_{gh}||_2
 <= ||S_g-P_g||_2 + ||S_h-P_h||_2
    + ||P_gP_h-P_{gh}||_2 + ||P_{gh}-S_{gh}||_2.
```

For permutations,

```text
||S-T||_{2,N}^2 = 2 d_H(S,T),
```

and traces transfer by Cauchy--Schwarz. Thus approximate multiplicative Markov models are equivalent to sofic models. This is `markov-sofic-equals-sofic`.

**Research consequence:** future positive attacks should target a table-dependent multiplicative Markov model, not a sophisticated final Birkhoff rounding theorem.

---

## 2. Proved: one-basis dephasing preserving inverses already forces monomiality

For `U in U(d)` put

```text
P_U(i,j)=|u_ij|^2.
```

If

```text
||P_UP_U^T-I||_{2,d} <= eps,
```

then there is a monomial unitary `M` such that

```text
d_2(U,M)^2 <= 2 eps.
```

Indeed set

```text
kappa(U)=1-(1/d)sum_{i,j}|u_ij|^4
        =1-tau(P_UP_U^T).
```

The hypothesis gives `kappa(U)<=eps`. Birkhoff averaging selects a permutation `sigma` with

```text
(1/d) sum_i |u_{i,sigma(i)}|^2 >= 1-kappa(U).
```

Choose the monomial support `sigma` and align phases with the selected matrix entries. Then

```text
d_2(U,M)^2
 <= 2-(2/d)sum_i |u_{i,sigma(i)}|^2
 <= 2 kappa(U)
 <= 2 eps.
```

This is `dephasing-inverse-forces-monomial`. Together with the existing `dephasing-destroys-multiplicativity`, it explains why ordinary unistochastic dephasing is not an easy bridge: if it preserved composition and inverses, the hard monomialization problem would already have been solved.

---

## 3. Balanced amplification remains useful, but it does not classicalize the assignment

The first divergent sprint proved the phase-safe balanced amplification estimate. If

```text
B(U)=U tensor bar(U)
```

and `delta=d_2(U,V)`, then

```text
d_2(B(U)^{tensor m},B(V)^{tensor m})^2 <= 2m delta^2,
tau(B(U)^{tensor m}) = |tau(U)|^{2m}.
```

Thus one may choose `m -> infinity` while keeping `m delta^2 -> 0`, obtaining many phase-free replicas and rapidly sharpening nontrivial traces.

### New no-go: de Finetti across those replicas is already saturated

On Hilbert--Schmidt space let `xi=I/sqrt(d)` and let left multiplication by a representation `pi(g)` act on `xi`. The coefficient is `chi(g)`. After conjugate doubling, one replica has coefficient `|chi(g)|^2`, and `m` replicas at

```text
(xi tensor bar(xi))^{tensor m}
```

have coefficient `|chi(g)|^{2m}`. This vector is already a **pure product across the replica blocks**.

Therefore a de Finetti theorem whose conclusion is merely “close to a mixture of product states across replicas” has nothing left to classicalize in that split. This is `replica-definetti-saturation-no-go`, which invalidates `definetti-via-independent-balanced-replicas`.

The corrected `definetti-group-table-rounding` target now requires the symmetric extension to live over **assignment/context/path variables inside the finite group-table encoding**. Balanced replicas can still solve the parameter problem, but they do not solve the tensor-split problem.

---

## 4. Exact bosonic calculation: the canonical second-moment endpoint is Haar-isotropic, not permutation-like

This supporting result is preserved here rather than as a separate graph vertex.

Let `P_n` be the projection onto `Sym^n(C^d)`, `D_n=binom(d+n-1,n)`, and

```text
|Omega_{n,d}> = vec(P_n)/sqrt(D_n).
```

Let `rho_{n,d}` be the marginal on one unbarred and one barred register. By `U tensor bar(U)` invariance it is isotropic:

```text
rho_{n,d} = beta I + gamma |Omega_d><Omega_d|,
beta  = (n-1)/(d n (d+1)),
gamma = (d+n)/(n(d+1)).
```

Its maximally-entangled fidelity is

```text
F_{n,d}=(d+n-1)/(dn).
```

The Haar separable isotropic state is

```text
sigma_d = I/(d(d+1)) + |Omega_d><Omega_d|/(d+1),
```

and exactly

```text
||rho_{n,d}-sigma_d||_2
 = (d-1)/(n sqrt(d^2-1))
 <= 1/n.
```

For unitaries `U,V`,

```text
Tr[rho_{n,d}(U tensor bar(V))]
 = d(n-1)/(n(d+1)) tau(U) overline(tau(V))
   + (d+n)/(n(d+1)) tau(UV*).
```

At the separable endpoint, the relative coherent term has coefficient `1/(d+1)`.

### Proved general ceiling

If a separable state `rho` is `U tensor bar(U)` invariant and

```text
rho=beta I + gamma |Omega_d><Omega_d|,
```

then

```text
gamma <= 1/(d+1).
```

A product state has maximally-entangled fidelity at most `1/d`, hence every separable state does; solving the isotropic trace/fidelity equations gives the bound. This is `covariant-separable-relative-signal-ceiling`, and it invalidates the direct `definetti-via-covariant-second-moments` route.

**Interpretation:** a covariant separable **second-moment** classicalization cannot retain a dimension-free fraction of relative unitary coherence. Higher-order/whole-table de Finetti remains open.

---

## 5. Proved: Haar random intermediate bases give exactly the same depolarizing channel

Let `U,V` be fixed, let `B_1,B_3` be endpoint bases, and let `B` be a Haar-random intermediate basis. Put

```text
A=B*UB_1,
C=B_3*VB,
D=B_3*VUB_1,
P_X=|X|^2.
```

A Haar two-design identity gives, for unit vectors `a,b` and a random orthonormal basis `{y_j}`,

```text
E sum_j |<a,y_j>|^2 |<y_j,b>|^2
 = (1+|<a,b>|^2)/(d+1).
```

Applying it entrywise yields the exact formula

```text
E_B[P_C P_A]
 = (J+P_D)/(d+1)
 = (d/(d+1))(J/d) + (1/(d+1))P_D.
```

This is `haar-random-basis-depolarization` and invalidates `markovization-via-random-intermediate-basis`.

The same coefficient `1/(d+1)` in the bosonic endpoint and random-basis dephasing is not coincidence: both are Haar second-moment calculations. Thus three superficially different ideas collapse to the same mechanism:

1. canonical bosonic second-moment de Finetti;
2. Haar random pure-state sampling;
3. Haar random intermediate-basis dephasing.

All retain one part in `d+1` of coherent information plus a depolarized background. This does **not** by itself rule out external statistical amplification; what remains missing is one common latent coupling whose deterministic maps compose.

---

## 6. The major surviving positive gate: regular-character Markovization

`regular-character-markovization` asks:

> For every fixed finite group table `T` and `eps>0`, is there `delta>0` such that every `delta`-accurate regular-trace unitary microstate of `T` produces, on some state space allowed to depend on the whole table, doubly stochastic kernels `P_g` with product defect, identity defect, and nontrivial trace all below `eps`?

The output is allowed to introduce hidden variables, increase dimension arbitrarily, and depend globally on the full finite table. It must **not** be a pointwise map `U -> P_U`; Cairn already proves universal pointwise unitary-to-finite-permutation rounding is impossible because `U(d)` is divisible.

If this Markovization theorem holds, `markov-sofic-equals-sofic` immediately proves hyperlinear implies sofic.

### Failed Markovization attempts

- **Ordinary one-basis dephasing:** killed by interference; the existing `sofic-model-via-unistochastic-dephasing` route remains invalidated by `dephasing-destroys-multiplicativity`.
- **Fresh random intermediate bases:** killed in expectation by the exact depolarizing formula above.
- **Heat/entropic smoothing:** does not evade integrality. If the smoothed Markov kernels also satisfy inverse products near `I`, the approximate-inverse theorem drives them toward deterministic permutations; smoothing still has to solve the joint quantization problem.
- **Independent generator discretizations:** pairwise good kernels need not share one latent state space and need not compose.
- **Independent nearest-neighbor spherical matchings:** geometric closeness of two chosen sample points does not make their indices equal; Hamming distance charges a full error.

---

## 7. NC-CSP connection: multiplication is a ternary, not pairwise, consistency problem

For a multiplication relation `gh=k`,

```text
||U_gU_h-U_k||_2^2
 = 2-2 Re tau(U_h*U_g*U_k).
```

This is intrinsically a **three-operator trace**. Culf--Mousavi--Spirig introduce relative distributions as a key tool for noncommutative 2-CSP approximation. The Q3.4 analogue needs a higher-order object compatible over an entire finite multiplication table.

The canonical open node is `permutation-valued-ternary-relative-distribution`:

> construct a dimension-free contextual joint law for the table's triples, compatible on overlapping associativity squares, whose pair marginals recover suitable relative distributions and whose endpoint is a common latent family of partial bijections or multiplicative bistochastic kernels.

A scalar three-variable relative distribution is insufficient. Scalar roots of unity commute and would round only an abelianized shadow. The classical alphabet has to be permutation-valued / quantum-magic / common-latent.

### Pair-groupoid coordinates

Writing

```text
X_{a,b}=U_a*U_b
```

gives the exact flat law

```text
X_{a,b}X_{b,c}=X_{a,c}.
```

Many multiplication comparisons become pairwise closeness statements in these coordinates. This is useful organization, but triangle flatness is itself a contextual ternary constraint; it does not remove the hard step.

### Finite-order normalization

A supporting lemma from the sprint: for every `U in U(d)` and integer `k>=2`, rounding each eigenphase to the nearest `k`th root gives `V^k=I` and

```text
d_2(U,V) <= 2 sin(pi/(2k)) <= pi/k.
```

For a finite table the product defect increases by at most `3 pi/k` and trace error by at most `pi/k`. Thus NC-CSP implementations that require finite-order operator alphabets can obtain them without a dimension-dependent price. Finite order does not make the operators commute.

---

## 8. A new outside connection: bounded-width CSPs have no operator satisfiability gap

Bulatov--Zhivny, *Satisfiability of commutative vs. non-commutative CSPs*, arXiv:2404.11709, prove that tractable finite-domain CSPs of bounded width have no classical/operator satisfiability gap. Cairn imports exactly this statement as `bounded-width-operator-csp-no-gap`.

This is unusually well aligned with the **zero-gap** form of Q3.4: hyperlinearity supplies operator losses tending to zero; soficity asks for classical finite-action losses tending to zero.

The high-risk open node `bounded-width-regular-character-compiler` asks for a **quantum-sound** reduction from each fixed regular-character group-table loss to a bounded-width finite-domain CSP, with classical solutions decoding back to finite actions.

### Failed shortcut: “group multiplication is Mal'tsev, therefore bounded width”

This is false in the needed form. Coordinatewise

```text
m(a,b,c)=ab^{-1}c
```

does not preserve the nonabelian multiplication relation `xy=z` without reordering factors. Even in the abelian case, affine/linear-equation CSPs occupy the unbounded-width regime where contextual operator gaps occur. Classical pp-reductions can also fail to be quantum-sound because they silently assume commutativity.

The surviving question is whether the **regular-character face**, with its much stronger trace/normal-subgroup constraints, admits a robust quantum-sound compilation using commutativity gadgets or quantum-polymorphism/Galois machinery.

---

## 9. Traffic probability remains useful at finite defect, not as a new limiting invariant

For a genuine finite permutation action and a connected labeled traffic test graph, choose a root and spanning tree. Every non-tree edge yields a cycle word. The traffic moment is exactly the fraction of roots fixed by **all** those cycle words.

Therefore at a normal `0/1` character limit, connected permutation traffic moments are already forced to `0` or `1` by word membership. Traffic does not supply a new independent asymptotic invariant.

Its value is at finite defect: branching test graphs see simultaneous shared-vertex/path consistency that cycles (ordinary traces) do not.

The existing `traffic-branching-rounding-hierarchy` asks for a positive graph law near the permutation values. The new `branching-traffic-markov-reconstruction` asks for the missing realization theorem:

> enough near-canonical branching identities imply one common multiplicative doubly stochastic table.

This deliberately reconstructs a Markov model, not permutations; automatic Birkhoff integrality handles the endpoint.

The first computational experiment should enumerate forks, diamonds, theta graphs, and overlapping-cycle graphs, optimize their unitary traffic polynomials under finite table constraints, and search for a robust deviation from every Markov realization.

---

## 10. Coherent configurations remain a strong intermediate category

The first divergent sprint introduced the pair-space/orbital idea. A finite permutation action has a commutant with a canonical `0/1` orbital basis whose multiplication constants are nonnegative integers. A generic unitary representation has a semisimple C*-commutant but no distinguished integral orbital basis.

Balanced adjoint doubling is structurally natural here: for a permutation representation it is literally the action on ordered pairs. The open `coherent-configuration-orbital-rounding` program asks whether near-regular character data force an approximately integral orbital algebra.

The second sprint sharpens the endpoint: it is enough to extract a coherent relational/Markov structure; one should not insist on direct common-masa monomialization. Not every coherent configuration is schurian, so a final realization gate remains.

---

## 11. Geometry: only the joint hypergraph Schreier design survived stress testing

A normalized-HS microstate is a mean-square almost action on a high-dimensional sphere:

```text
E_x ||Ux-Vx||^2 = d_2(U,V)^2.
```

Regular trace separation makes nontrivial words move a typical point a constant distance. This motivates discretizing the sphere.

But independent nearest-neighbor/per-generator matching fails because Hamming equality is literal index equality, not geometric closeness. General partition-induced Markov kernels and entropic smoothing also do not solve the inverse/integrality gate.

The surviving `geometric-schreier-design` route is genuinely joint: build one colored candidate hypergraph encoding all generator transitions and table relations, prove degree/codegree quasirandomness from spherical concentration/trace separation, then use a matching/design/absorption theorem to select a common Schreier structure.

This remains the best geometrically independent positive route because it does not index the finite model by a Følner subset of the group.

---

## 12. CP versus CPSD, quantum magic squares, and quantum Latin squares: a finite separator language

Classical correlation data often live in completely positive (CP) cones, while finite-dimensional quantum data live in completely positive semidefinite (CPSD) cones. The existing `group-table-cpsd-cp-face-collapse` program asks whether these closures coincide on the highly special regular-character group-table face.

The global cones do not coincide, and noncommutative Birkhoff-type dilation is false. Quantum magic squares and group-invariant quantum Latin squares reinforce the warning: positivity, bistochasticity, and even group symmetry do **not** automatically imply classical permutation structure.

This makes CP/CPSD and matrix-convex machinery valuable in two directions:

- **positive:** prove collapse on the regular group-table face;
- **negative:** find an explicit dual trace/graph polynomial with quantum infimum zero and classical finite-action infimum bounded away from zero.

A local quantum/classical gap is not enough for a negative Q3.4 solution; it still has to be coherently groupified.

---

## 13. Negative-program constraint: exact finite-dimensional gadgets are usually too classical globally

A generic pseudo-telepathy game, quantum Latin square, or exact finite-dimensional operator solution does not produce a hyperlinear nonsofic group. If one simply takes the group generated by a fixed finite-dimensional unitary gadget, one obtains a linear group; finitely generated linear groups are residually finite/sofic.

More generally, a finitely generated maximally almost periodic group whose finite-dimensional unitary representations separate points is residually finite: finitely many representations separate any fixed nontrivial element after taking a direct sum, and the finitely generated linear image is residually finite by Mal'cev. Thus **MAP visibility cannot be the nonsofic mechanism**.

Current Cairn already contains the relevant Peter--Weyl/profinite and projective-kernel infrastructure, so this is retained here as a design constraint rather than duplicated as a new node.

A genuine negative construction would need all of:

1. nested coherence across increasing finite windows;
2. regular trace on all nontrivial tested words;
3. relator normalized-HS error tending to zero;
4. one fixed robust classical finite-action loss gap;
5. nonliftability/MAP avoidance so the construction never collapses to an exact linear representation.

The right moonshot is therefore a **regular-character contextual self-test**, not merely a quantum advantage.

---

## 14. Exact projective-kernel polarization: informative, but the soft-to-exact gate remains

Balanced tensor powers of an exact finite-dimensional representation polarize its normalized character to the `0/1` character of its scalar/projective kernel. The quotient by that projective kernel embeds through the adjoint representation into a finite-dimensional linear group and is therefore sofic/residually finite.

Current Cairn already canonicalizes this as the character Diracization/projective-kernel lane. The unsolved issue is exactly the one relevant to hyperlinear microstates: near-relators are only **near** the projective kernel, not actually in it. A dimension-free theorem turning soft projective-kernel membership into exact projective-kernel membership would be another positive solution, but that is already represented and is not duplicated here.

---

## 15. The positive-loss/minimax formulation suggests a weaker target than pointwise rounding

Current Cairn's positive-loss certificate says a negative Q3.4 answer would yield one finite nonnegative classical loss with a fixed positive gap, while hyperlinear character models make the corresponding quantum loss tend to zero.

Therefore it would already suffice, for each fixed finite table/loss `T`, to prove **any** table-dependent modulus

```text
OPT_classical(T) <= f_T(OPT_quantum(T)),
f_T(x) -> 0 as x -> 0.
```

No pointwise rounding map is required. Even an atrocious table-dependent power law would settle that finite obstruction. This is the most natural doorway for CSP approximation, Grothendieck-type inequalities, SOS hierarchies, and dual-cone methods.

This observation is already close to current Cairn's uniform-gap equivalences, so it is used as strategy rather than duplicated as a new root claim.

---

## 16. Multi-marginal optimal transport: useful only with a special integrality theorem

For a unitary table and word set `W`, the coupling

```text
gamma_U = (x -> (U_h x)_{h in W})_# mu
```

on the sphere has uniform marginals and low group-law transport cost. A finite sofic model would be a very special equal-weight atomic Monge coupling in which every coordinate map is a permutation of one common finite set.

General multi-marginal transport has fractional/non-Monge optimizers, so there is no generic Birkhoff theorem to quote. The only credible form is the existing geometric/hypergraph program: exploit the special group costs and high-dimensional quasirandomness to prove integral design selection.

---

## 17. Lattice gauge theory moonshot

A finite presentation/table can be viewed as a finite 2-complex. A unitary microstate is a low-energy `U(d)` lattice gauge field; relator traces are Wilson-loop observables near the identity while designated nontrivial words have regular-character trace near zero. A sofic model is the corresponding `S_N`/Hamming gauge field.

A speculative theorem would say:

> zero regular `U(N)` Wilson loss on a fixed finite presentation complex implies zero symmetric-group Hamming Wilson loss.

Potential tools include exact finite-`N` character expansions, Schur--Weyl/partition-algebra identities, walled-Brauer calculus, and surface/spin-foam expansions. Recent finite-`N` Wilson-loop dualities make the comparison mathematically concrete.

**Failure mode:** entropy/free-energy comparison is not enough. Hyperlinearity is an existence statement and may be witnessed by exponentially rare microstates. A useful theorem must transfer zero-loss configurations or a zero-energy gap, not merely thermodynamic limits.

This remains a moonshot artifact idea rather than a canonical Cairn vertex.

---

## 18. Arithmetic/tropical route: the obvious reduction fails

Approximate complex polynomial relations do not become exact finite-field relations merely by choosing a prime; small Euclidean size has no reason to imply divisibility. Exact finite-dimensional matrix models would often imply much stronger LEF/residual-finiteness behavior than soficity.

A viable arithmetic version would need a dimension-free **normalized-rank/statistical Nullstellensatz**: near-vanishing group-word relations in normalized trace/HS should yield exact algebraic relations on `1-o(1)` of a finite module. No theorem of that strength is currently available.

Entrywise tropical/argmax rounding also fails naively: Fourier/Haar-flat unitaries have enormous magnitude ties, and generic tie-breaking destroys multiplication coherence. The only credible argmax use is constraint-aware, at a whole-table symmetric-extension or traffic level.

---

## 19. Complete failed-attempt ledger from the sprint

These failures are preserved even where they do not deserve individual graph routes.

### KILLED A — De Finetti across independent balanced replicas

Already product across the copy split; no assignment classicality is created. Canonical invalidation: `replica-definetti-saturation-no-go`.

### KILLED B — Canonical bosonic second moments directly yield permutations

They converge to the Haar separable isotropic state, with only `1/(d+1)` relative coherent coefficient.

### KILLED C — Random intermediate basis makes dephasing multiplicative on average

Exact formula: `(J+P_D)/(d+1)`, not `P_D`. Canonical invalidation: `haar-random-basis-depolarization`.

### KILLED D — Ordinary entrywise dephasing plus Birkhoff

`|UV|^2 != |U|^2|V|^2` because interference is discarded before relations are enforced. Already represented by `sofic-model-via-unistochastic-dephasing` and `dephasing-destroys-multiplicativity`.

### KILLED E — Convex mixtures of monomial matrices retain dimension-free correlation

Diffuse unitary blocks spread their mass across too many monomial supports; no dimension-free coherent overlap survives without additional common latent structure.

### KILLED F — Independent random-hyperplane hashes

Random hyperplanes give a useful dimension-free HS-to-bit disagreement estimate but the hashes do not compose, so they are only local observables inside another global rounding mechanism.

### KILLED G — Independent nearest-neighbor point-cloud matchings

Geometric closeness does not imply equality of sample indices; Hamming error remains macroscopic unless the matchings are selected jointly.

### KILLED H — Generic partition/Koopman Markovization

Partition kernels need not satisfy multiplication on one common finite state space; approximate inverse composition again pushes them toward deterministic structure.

### KILLED I — Heat/entropic Markov smoothing

Smoothing can improve transport regularity but cannot evade the inverse law: a smoothed doubly stochastic approximate inverse is already near a permutation.

### KILLED J — Exact spectral fixed-space extraction

HS-small relators need not have a large exact fixed subspace uniformly enough across all relations and witnesses; spectral cuts can destroy compatible multiplication.

### KILLED K — HS-to-normalized-rank / Dowling conversion

Small normalized HS norm does not imply small normalized rank. Tiny singular values can occupy full rank, so almost multilinear/rank-metric machinery cannot be imported for free.

### KILLED L — Generic dimension compression

Hyperlinear profiles can force severe dimension growth; no uniform low-dimensional compression preserves arbitrary finite-table HS relations and trace separation.

### KILLED M — “Finite-dimensional representations separate, therefore counterexample”

The opposite: finitely generated MAP visibility drives toward residual finiteness/soficity.

### KILLED N — Generic scalar NC-CSP rounding

Scalar roots of unity commute and therefore only round an abelianized shadow of a nonabelian permutation table.

### KILLED O — “Group law is automatically bounded-width Mal'tsev”

The nonabelian multiplication relation is not preserved by the naive coordinatewise Mal'tsev operation; affine cases are unbounded-width/contextual territory anyway.

### KILLED P — Traffic moments provide a new independent invariant at the normal `0/1` limit

Connected permutation traffic moments reduce to simultaneous fixed-point events and are already forced at a normal Dirac limit. Traffic is useful only quantitatively at finite defect.

### KILLED Q — Generic quantum magic/Latin gap implies a nonsofic group

A fixed exact finite-dimensional gadget generates a linear/sofic group. A negative solution needs a coherent nonliftable asymptotic family with regular trace.

### KILLED R — Naive algebraic reduction modulo `p`

Euclidean near-zero does not imply modular zero; the topology is wrong.

### KILLED S — Entropy alone transfers existence

Free-energy or counting asymptotics can ignore rare zero-loss configurations, while hyperlinearity is purely existential.

---

## 20. Surviving targets, ranked

### 1. Table-dependent regular-character Markovization

Best positive formulation. It asks only that phase/interference be removed while preserving multiplication, inverses, and trace on one common finite state space. `markov-sofic-equals-sofic` does the rest.

### 2. Whole-table permutation-valued ternary relative distribution

Best analytic route into Markovization. The key is compatibility around associativity squares and a nonabelian classical alphabet.

### 3. Quantum-sound bounded-width regular-character compiler

Most surprising outside connection. If the regular-character face can be compiled robustly to bounded width, the imported no-gap theorem supplies the quantum-to-classical step.

### 4. Branching-traffic-to-Markov reconstruction

Best moment-hierarchy route. Search small branching graphs first for either a reconstruction pattern or a robust separator.

### 5. Coherent-configuration integerization

Best algebraic-combinatorial alternative to a common masa. Work in pair-space/orbital multiplication constants rather than basis vectors.

### 6. Joint geometric Schreier hypergraph design

Best geometrically independent route. The theorem must choose all generator matchings simultaneously via quasirandom hypergraph design/absorption.

### 7. Zero-temperature `U(N)` to `S_N` gauge universality

Highest-risk positive moonshot, using exact character/surface expansions rather than second moments.

### 8. Regular-character contextual self-test

Cleanest nontraditional negative specification: a nested, nonliftable quantum family with regular trace and one robust classical finite-action gap.

---

## 21. Concrete computations to run next

1. **Tiny Markovization search.** On the smallest associativity square, optimize over unitary tables and over common-state doubly stochastic tables; search for a dimension-independent inequality or a stable gap.
2. **Branching traffic SDP.** Enumerate connected labeled graphs with 3--6 vertices, excluding pure cycles; optimize deviation from the canonical Markov/permutation value under unitary table constraints.
3. **Quantum-magic group-table face.** Build the smallest regular-character matrix-convex relaxation and search for exposed nonclassical extreme points that survive associativity/inverse constraints.
4. **Quantum-polymorphism test.** Compute the polymorphism behavior of the finite relation language underlying the regular-character compiler and test whether a quantum-sound bounded-width reduction is algebraically plausible or formally obstructed.
5. **Coherent orbital integerization.** Numerically compute pair-space commutants of small exact/near unitary tables and search for positive approximately disjoint bases with near-integral multiplication constants.
6. **Hypergraph Schreier feasibility.** For random spherical microstate tables, compare pairwise generator matchability with joint relation-preserving matching feasibility; measure degree/codegree statistics relevant to absorption.

---

## 22. Conditional proof skeleton if Markovization falls

Assume `regular-character-markovization`.

1. Fix a finite window `F` in a hyperlinear group and target Hamming error `eps`.
2. Include identity, inverse pairs, and all tested products in the table.
3. Request a sufficiently accurate regular-trace unitary microstate from hyperlinearity.
4. Apply Markovization to obtain doubly stochastic kernels `P_g` with small product, identity, inverse, and trace defects.
5. Apply `birkhoff-approx-inverse-permutation` to every `P_g`, obtaining permutations `S_g` with Frobenius error `O(sqrt(eta))`.
6. Transfer multiplication through the operator-norm-one kernels.
7. Convert squared Frobenius error between permutations to Hamming error using `||S-T||_2^2=2d_H(S,T)`.
8. Transfer trace separation to fixed-point separation.
9. Let `eta -> 0`; this gives a sofic approximation of `F`.

There is no remaining integrality theorem after step 4.

---

## 23. Conditional negative skeleton if a regular contextual gap is found

A credible negative program must produce a fixed finite classical loss `L` and a nested sequence of approximate unitary group tables such that

```text
quantum loss -> 0,
classical finite-action loss >= c > 0,
```

while maintaining coherence over all increasing windows and regular trace on every tested nontrivial word. The local gap must never be realized by one exact finite-dimensional representation, or linear/MAP residual finiteness destroys the intended obstruction. One then uses compactness/diagonalization to assemble a hyperlinear group and the fixed classical loss to certify nonsoficity.

This is substantially stronger than finding a pseudo-telepathy game or a CP/CPSD gap.

---

## 24. Literature that materially informed this sprint

Primary references:

- P. Burton, M. Chaudkhari, K. Juschenko, K. Muliarchyk, *Hyperlinear approximations to amenable groups come from sofic approximations*, arXiv:2311.09202.
- F. G. Jeronimo, P. Wu, H. Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590.
- M. Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986.
- E. Culf, H. Mousavi, T. Spirig, *Approximation Algorithms for Noncommutative CSPs*, arXiv:2312.16765.
- A. A. Bulatov, S. Zhivny, *Satisfiability of commutative vs. non-commutative CSPs*, arXiv:2404.11709.
- L. Ciardo, G. Joubert, A. Mottet, *Quantum Polymorphisms and Commutativity Gadgets*, arXiv:2511.23445.
- E. Culf, J. van Dobben de Bruyn, P. Zeman, *Quantum polymorphism characterisation of commutativity gadgets in all quantum models*, arXiv:2604.01408.
- G. De las Cuevas, T. Drescher, T. Netzer, *Quantum magic squares: dilations and their limitations*, arXiv:1912.07332.
- A. S. Arnadottir, D. E. Roberson, *Group Invariant Quantum Latin Squares*, arXiv:2501.00196.
- J. Sikora, A. Varvitsiotis, *Linear conic formulations for two-party correlations and values of nonlocal games*, arXiv:1506.07297.
- M. Laurent, T. Piovesan, *Conic approach to quantum graph parameters using linear optimization over the completely positive semidefinite cone*, arXiv:1312.6643.
- C. Male, *Traffic distributions and independence*, arXiv:1111.4662.
- I. Charlesworth et al., *Random permutation matrix models for graph products*, arXiv:2404.07350.
- L. Kuhne, G. Yashfe, *On entropic and almost multilinear representability of matroids*, arXiv:2206.03465.
- W. Slofstra, *The hyperlinear profile of groups*, arXiv:1806.05267.
- B. Pass, *Multi-marginal optimal transport: theory and applications*, arXiv:1406.0026.
- P. Keevash, *Hypergraph matchings and designs*, arXiv:1807.05752.
- U. Haagerup, M. Musat, *Factorization and dilation problems for completely positive maps on von Neumann algebras*, arXiv:1009.0778.
- T. Lemoine, *Universal dualities for Wilson loops in lattice Yang--Mills*, arXiv:2604.16252.
- T. Lemoine, *Gaussian measure on the dual of U(N), random partitions, and 2D Yang--Mills*, arXiv:2405.08393.
- A. Alekseev, A. Thom, *Centralizers of sofic approximations of Kazhdan groups*, arXiv:2608.05362.

---

## 25. Final assessment

No solution of Q3.4 is claimed.

The strongest proved progress is the **automatic-integrality reduction**: multiplicative Markov models already round to sofic models because inverse relations force doubly stochastic kernels to Birkhoff extreme points.

The strongest negative progress is the **second-moment collapse/no-go**: independent replica de Finetti is saturated from the start, canonical covariant separability attenuates relative coherence by at least the `1/(d+1)` factor, and Haar random-basis dephasing is exactly the same depolarizing mechanism.

The most useful surviving research question is therefore no longer

> “How do we round each unitary matrix to a permutation?”

but

> **“How do we globally classicalize the composition law of one finite regular-trace unitary table into one multiplicative Markov law?”**

If that gate falls, the proved Birkhoff approximate-inverse theorem does the rest.
