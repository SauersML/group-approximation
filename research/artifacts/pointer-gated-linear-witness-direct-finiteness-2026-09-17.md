# Pointer-gated linear Bernoulli witnesses and direct finiteness of F_q[G]

Agent `a-gs-window-transport`, wave `swarm-0917`, 2026-09-17. Target hole:
`rokhlin-window-transport-is-dominated` (condition (D): `I(x(1); y_F) <= H(y_1)` for every
configuration).

## 0. Summary

Every known configuration with `Phi -> 0` has the same structure. A nonlinear pointer chooses which
linear functional of the value inputs a codeword outputs. Examples are the star of Example 5 in
`research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md`, the parity gadget of
Theorem A in `research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md`, and the tree
star in Section 6.1 of that artifact. This note splits the deficit of such codes into two
independent parts and kills the linear part on groups whose group ring is directly finite.

1. **Theorem 1 (exact split).** For a pointer-linear code `psi = (J, L_J)`, on every incidence
   pattern:

       gap(psi) = gap(J) + log q · ( E d(J_F) - E r(J_1) ).

   Here `gap(.) = I(input at 1 ; outputs on F) - H(output at 1)`. `d` is the number of value
   dimensions at site 1 that the gated linear outputs recover, and `r` is the rank of the gated
   linear output.
2. **Theorem 3 (direct finiteness bounds the value part).** Suppose `psi` is gated
   monomial-diagonal: on value coordinate `i` a codeword outputs a scalar times a group translate of
   one fixed functional `T_i` in `F_q[G]`, or nothing. If `F_q[<E ∪ F>]` is directly finite, then
   `E d <= E r`, so `gap(psi) <= gap(J)`. The only step that uses a hypothesis on `G` is uniqueness
   of the left inverse of `T_i`.
3. **Proposition 5 (abelian homomorphic pointers).** If `J` is a homomorphism for some finite abelian
   group structure on the pointer alphabet, then `gap(J) <= 0` on every pattern. This is the
   character form of the constants argument.
4. **Corollary 6 (the class dies).** Take a gated monomial-diagonal code whose pointer is abelian
   homomorphic, such as the parity gadget and the split star.
   - Over every group `G` with `F_q[<E ∪ F>]` directly finite it satisfies (D) on every incidence
     pattern.
   - If it violates (D) over `G`, some `T_i` is a one-sided unit of `F_q[G]`. By Seward's Corollary
     4.1, `h^Rok_sup(G) < infinity`, so `rho_{q'}(G) = 0` for every `q'`.
   - So the class can never be the first evidence of a deficit. Any member with a deficit lives on a
     group where Kaplansky's direct finiteness conjecture already fails and Rokhlin entropy already
     collapses.
5. **Calibration (Section 5).** In the finite loop of Theorem B the split parity gadget has
   `E d ≈ 4` against `E r = 1`. So `E d <= E r` fails for abstract cancellative patterns and holds on
   directly finite groups, and associativity enters through uniqueness of inverses. Theorem C of the
   firewall is the one-pattern shadow.
6. **Where it stops (Section 6).**
   - The method fails for gated linear codes that mix coordinates, or that output several
     functionals on one coordinate. A column has many left inverses even over commutative rings, and
     the trace substitute is only defined mod `p`.
   - The general rank inequality `E d <= E r` (RELD) holds over finite groups by counting (Prop 8).
     It is OPEN over infinite groups, as `pointer-gated-linear-codes-are-rank-dominated`.

## 1. Setup

- `G` is a countable group and `q` a prime power, `A = F_q`.
- A configuration `(k, E, F, psi)` has `x` iid uniform on `(A^k)^G` and `y_g = psi(x|_{gE})`, as in
  `bernoulli-rokhlin-deficit-has-a-finitary-witness`.
- Write `gap(psi) = I(x(1); y_F) - H(y_1)`. Then

      Phi = (1/k)[ H(y_1) + k log q - I(x(1); y_F) ] = log q - gap(psi)/k ,

  so `Phi < log q` iff `gap(psi) > 0`. A witness is a configuration with `gap > 0`.

**Pointer-linear codes.**
- Split the `k` coordinates into pointer coordinates `[k_P]` and value coordinates `[k_V]`, with
  `k = k_P + k_V`. So `x(g) = (p(g), v(g))`, with `p(g) ∈ A^{k_P}` and `v(g) ∈ F_q^{k_V}`.
- A pointer-linear code is

      psi(x|_E) = ( J(p|_E) , L_{J(p|_E)} (v|_E) ),

  where `J` takes values in a finite set `Jset` and each `L_j : F_q^{E × k_V} -> F_q^{m}` is
  `F_q`-linear.
- Put `J_g = J(p|_{gE})` and `Z_g = L_{J_g}(v|_{gE})`.
- The pointer configuration `(k_P, E, F, J)` is itself a configuration on `k_P` coordinates. Its gap
  is `gap(J) = I(p(1); J_F) - H(J_1)`.

**Functionals as group-ring elements.** A linear functional on `F_q^{G}` with finite support is
`v ↦ Σ_g a_g v(g)`. Identify it with `a = Σ_g a_g g ∈ F_q[G]`. Suppose `L_j` has row `s` given by
`v|_E ↦ Σ_{e ∈ E} Σ_i c^{(j,s)}_{e,i} v_i(e)`. Then at codeword `f` the output functional on
coordinate `i` is

    v_i ↦ Σ_e c^{(j,s)}_{e,i} v_i(f e)   ↔   f · T^{(j,s)}_i ,   T^{(j,s)}_i = Σ_e c^{(j,s)}_{e,i} e ,

using `f(e) = (fe)` in `G`. This is the only place where the group law is used.

## 2. Theorem 1: the exact split

For `j_F ∈ Jset^F` let `L(j_F)` be the linear map `v|_W -> (Z_f)_{f ∈ F}`, where
`W = FE ∪ {1}` and `J_F = j_F`. Let `P_1` be the projection `v|_W -> v(1)`. Define

    d(j_F) = dim( row P_1 ∩ row L(j_F) )     and     r(j) = rank L_j .

**Theorem 1.** On every incidence pattern, and for any finite set `Jset` and any function `J`:

    gap(psi) = gap(J) + log q · ( E d(J_F) - E r(J_1) ) .

*Proof.*

1. **Pointer term.** `J_F` is a function of `p`, and `v` is independent of `p`. So
   `I(x(1); J_F) = I(p(1); J_F) + I(v(1); J_F | p(1)) = I(p(1); J_F)`.
2. **Chain rule.** `I(x(1); y_F) = I(x(1); J_F) + I(p(1), v(1); Z_F | J_F)`.
3. **Pointer drops out of the value term.** Write the last term as
   `I(v(1); Z_F | J_F) + I(p(1); Z_F | J_F, v(1))`.
   - Since `v ⊥ p` and `J_F` is a function of `p`,
     `P(p(1)=a, v=w | J_F=j) = P(p(1)=a | J_F=j) P(v=w)`.
   - So `v ⊥ p(1)` given `J_F`.
   - `Z_F` is a function of `(J_F, v)`, so the second term is `0`.
4. **Linear mutual information.** Given `J_F = j_F`, `v|_W` is uniform and `Z_F = L(j_F) v|_W`. For
   linear maps `P, L` on a uniform vector,

       I(Pv; Lv) = (rk P + rk L - rk [P; L]) log q = dim(row P ∩ row L) log q .

   So `I(v(1); Z_F | J_F) = E d(J_F) log q`.
5. **Output entropy.** `H(y_1) = H(J_1) + H(Z_1 | J_1)`. Given `J_1 = j`, `Z_1` is uniform on the
   image of `L_j`. So `H(y_1) = H(J_1) + E r(J_1) log q`.
6. Subtract. QED

The proof uses only the independence of `p` and `v` and linearity in `v`. It holds on abstract
patterns (partial Latin rectangles), including the finite loops of the firewall.

**Corollary 2 (reduction).** If `E d(J_F) <= E r(J_1)` for a pointer-linear `psi`, then `gap(psi) > 0`
implies `gap(J) > 0`. A value-linear witness then forces a witness on the `k_P < k` pointer
coordinates, with the same `E` and `F`. If `J` is itself pointer-linear, iterate.

## 3. Theorem 3: gated monomial-diagonal codes over directly finite group rings

**Definition.** A pointer-linear code is *gated monomial-diagonal* if there are:
- nonzero `T_1, ..., T_{k_V} ∈ F_q[G]`;
- for each pointer value `j`, a set `I_j ⊆ [k_V]` of active coordinates;
- for each `i ∈ I_j`, a scalar `γ_{i,j} ∈ F_q^×` and a group element `h_{i,j}` with
  `supp(h_{i,j} T_i) ⊆ E`;

such that `L_j` outputs exactly one functional `γ_{i,j} h_{i,j} T_i` on coordinate `i` for each
`i ∈ I_j`, and nothing else. Then `r(j) = |I_j|`.

- The pointer chooses which coordinates are read, and where the read pattern sits inside the window.
- The functional on a coordinate is fixed up to a trivial unit.

**Normalization.** Fix one `j_0` with `i ∈ I_{j_0}` and replace `T_i` by `h_{i,j_0} T_i` and
`h_{i,j}` by `h_{i,j} h_{i,j_0}^{-1}`. Then `supp T_i ⊆ E`. Since `h_{i,j} supp(T_i) ⊆ E`, also
`h_{i,j} ∈ E E^{-1}`. Assume this from now on, so `T_i` and every `f h_{i,j}` lie in `K = <E ∪ F>`.
Coordinates that are never active contribute nothing and are dropped.

Examples:
- **Split star (Example 5).** `T_i = e_0` and `I_j = {j}`.
- **Parity gadget (Theorem A).** `T_i = Ê = Σ_{e ∈ E_val} e` and `I_j = {j}`.
- **Not covered: the tree star of firewall 6.1.** It outputs `d` functionals on the selected
  coordinate. That structure is also not a group.

**Lemma 2 (recovery criterion).** Let `S_i = {(f, j) : f ∈ F, J_f = j, i ∈ I_j}`. Then
`d(J_F) = Σ_i d_i`, where `d_i ∈ {0, 1}` and

    d_i = 1   iff   a T_i = 1  for some  a ∈ span_{F_q} { f h_{i,J_f} : (f, J_f) ∈ S_i } .

*Proof.*
- Both `row L(J_F)` and `row P_1` are direct sums over coordinates: `L(J_F)` is diagonal, and
  `row P_1 = ⊕_i span{v_i(1)}`.
- For subspaces `U = ⊕ U_i` and `W = ⊕ W_i` graded by the same decomposition, `U ∩ W = ⊕ (U_i ∩ W_i)`.
- On coordinate `i`, `row L(J_F)` is `{ a T_i : a ∈ span{ f h_{i,J_f} } }`, by the identification of
  Section 1 and `f · (γ h T_i) = γ (f h) T_i`.
- `span{v_i(1)}` is the one-dimensional space spanned by `1 ∈ F_q[G]`. QED

**Theorem 3.** Let `psi` be gated monomial-diagonal, `K = <E ∪ F>`, and suppose `F_q[K]` is directly
finite (`ab = 1` implies `ba = 1`). Then for every coordinate `i`:

    P(d_i = 1) <= P(i ∈ I_{J_1}) .

Hence `E d(J_F) <= E r(J_1)` and `gap(psi) <= gap(J)`.

*Proof.*

0. If `T_i` has no left inverse in `F_q[K]`, then `d_i = 0` always, by Lemma 2. So assume it has
   one.
1. **Uniqueness.** Suppose `a T_i = 1` with `a ∈ span{f h_{i,J_f}} ⊆ F_q[K]`. Direct finiteness
   gives `T_i a = 1`. Any other left inverse `a'` then satisfies `a' = a'(T_i a) = (a' T_i) a = a`.
   So the recovering `a` is the fixed element `T_i^{-1}`, whatever `J_F` is.
2. **Support.** If `d_i = 1`, then `supp T_i^{-1} ⊆ { f h_{i,J_f} : (f, J_f) ∈ S_i }`. Fix
   `g_0 ∈ supp T_i^{-1}`, which is nonempty. Then `d_i = 1` implies that for some `j` with
   `i ∈ I_j`, the codeword `f = g_0 h_{i,j}^{-1}` has `J_f = j`.
3. **Union bound and stationarity.** `J_g` has the same law for every `g`, because `p` is iid and
   `J_g = J(p|_{gE})`. So

       P(d_i = 1) <= Σ_{j : i ∈ I_j} P( J_{g_0 h_{i,j}^{-1}} = j ) = Σ_{j : i ∈ I_j} P(J_1 = j) = P(i ∈ I_{J_1}).

4. Sum over `i`: `E d <= Σ_i P(i ∈ I_{J_1}) = E |I_{J_1}| = E r(J_1)`. Apply Theorem 1. QED

**What direct finiteness is used for.** Suppose `a T = 1` but `T a != 1`. Then for every `b`,
`(a + b(1 - T a)) T = a T + b(T - T a T) = 1`. So the left inverses form the infinite affine space
`a + F_q[K](1 - T a)`, and step 1 fails. Uniqueness of the left inverse of a left-invertible element
is therefore equivalent to its being a unit. The hypothesis cannot be weakened inside this proof.

**Corollary 4 (explicit Kaplansky pair).** For a gated monomial-diagonal code over any group, suppose
`gap(psi) > gap(J)`.
- Then some normalized `T_i`, with `supp T_i ⊆ E`, has a left inverse
  `a ∈ span{f h_{i,j}} ⊆ F_q[F E E^{-1}]` with `T_i a != 1`.
- This follows from the proof: if every left-invertible `T_i` were a unit, the bound would hold.
- So `F_q[K]` is not directly finite, with a one-sided inverse pair supported in the window.

## 4. Abelian homomorphic pointers

**Proposition 5.** Let `M` be a finite abelian group and `B` an abelian group. Let `x` be iid Haar
on `M^G`, and let `psi : M^E -> B` be a homomorphism, possibly composed with a translation of `B`.
Then on every incidence pattern `I(x(1); y_F) <= H(y_1)`.

*Proof.*
- Translations change no entropy, so assume `psi` is a homomorphism. Let `W = FE ∪ {1}`, let `L` be
  the homomorphism `x|_W -> y_F`, let `K = ker L`, and let `π : M^W -> M` be evaluation at `1`.
- **Fibres.** Given `y_F`, `x|_W` is uniform on a coset of `K`, so `x(1)` is uniform on a coset of
  `π(K)`. So `I(x(1); y_F) = log |M / π(K)|`.
- **Characters.** Let `χ` be a character of `M` trivial on `π(K)`. Then `χ ∘ π` is trivial on `K`, so
  `χ ∘ π = Λ ∘ L` for a character `Λ` of `L(M^W)`.
- **Constants.** Evaluate at the constant `diag(c)`, `c ∈ M`. Every codeword outputs `Ψ c`, where
  `Ψ = psi ∘ diag_E`. So `χ(c) = Λ((Ψ c)_{f ∈ F})`, and `χ` is trivial on `ker Ψ`.
- **Count.** The dual of `M / π(K)` injects into the dual of `M / ker Ψ`. Finite abelian groups have
  as many characters as elements, so `|M / π(K)| <= |Ψ(M)| <= |psi(M^E)|`.
- `y_1` is Haar on `psi(M^E)`, so `H(y_1) = log |psi(M^E)|`. QED

For `M = F_q^k` this is Proposition 4 of the transport artifact. The pointer
`j = (p_1|_t + p_2|_t + p_3|_t) mod 2^t` of the gadget is a homomorphism for the group structure
`Z/2^t` on `t`-bit strings, and the uniform measure is Haar for it. So `gap(J) <= 0` for that pointer
on every pattern.

**Corollary 6.** Let `psi` be gated monomial-diagonal with an abelian homomorphic pointer.

1. If `F_q[<E ∪ F>]` is directly finite, then `gap(psi) <= 0`, i.e. (D) holds for this configuration
   on this pattern.
2. If `gap(psi) > 0` over `G`, then `F_q[G]` is not directly finite, with a pair supported in the
   window (Corollary 4).
   - By `infinite-rokhlin-supremum-forces-surjunctivity` (Seward, arXiv:1501.03367v4, Corollary
     4.1: `h^Rok_sup(G) = infinity` implies `K[G]` directly finite for every field `K`),
     `h^Rok_sup(G) < infinity`.
   - `G` is infinite, since group algebras of finite groups are directly finite. So every Bernoulli
     shift `(A'^{k'})^G` with `|A'| = q'` is free ergodic, with finite Rokhlin entropy at most
     `k' log q'`. Hence `h^Rok_G((A'^{k'})^G) <= h^Rok_sup(G) < infinity` for every `k'`.
   - So `rho_{q'}(G) = lim_{k'} h^Rok_G((A'^{k'})^G)/k' = 0` for every `q' >= 2`.

**Hosts where the class is dead on every pattern** (graph-established direct finiteness):
- groups linear sofic over `F_q` (`linear-sofic-group-algebra-is-stably-finite`), which includes all
  sofic groups;
- Higman's group and its subgroups (`higman-group-algebras-embed-in-division-rings`, established, not
  yet independently re-derived). No soficity is known there, and the sofic radical theorem gives
  nothing.
- On the binary Leavitt unit group `R^x` (nonsofic), direct finiteness of `F_2[R^x]` is OPEN
  (`leavitt-unit-group-algebra-is-directly-finite`). By Corollary 6, any gated monomial-diagonal
  binary deficit there is a Kaplansky counterexample.

## 5. Calibration: the split parity gadget in a finite loop

Modify Theorem A of the firewall so that pointer and value coordinates are disjoint:
- `k_P = t` pointer bits and `k_V = 2^t` value bits, so `k = 2^t + t`;
- `j = sum of the three pointer inputs mod 2^t`, and the output is `(j, XOR_{e ∈ E_val} v_e[j])`.

The pattern is unchanged, so (L) and (R) hold and Theorem B realizes it in a finite loop.

**Decoding.** As in the firewall artifact:
- the three codewords of gadget `g` share `j_g`;
- XOR of their outputs gives `v(o)[j_g]`;
- the `j_g` are iid uniform on `Z/2^t`, because the pointer sites of distinct gadgets are disjoint.

**Bound.** `H(y_1) = t + 1` bits, and `H(x(o) | y_F) <= t + k_V (1 - 1/k_V)^R`. With
`R = ceil(2 k_V ln k_V)`:

    Phi <= ( 2t + 1 + k_V (1 - 1/k_V)^R ) / ( 2^t + t )  bits .

Hand checks:
- `t = 2`: `R = 12`, residual `4 (3/4)^12 = 0.127`, `Phi <= 5.127/6 = 0.855 < 1`.
- `t = 3`: `R = 34`, residual `8 (7/8)^34 = 0.085`, `Phi <= 7.085/11 = 0.644`.

**Decomposition in the loop.**
- `gap(J) <= 0` by Proposition 5, which is pattern-level.
- `E r = 1`, since exactly one value coordinate is active.
- `E d >= k_V (1 - (1 - 1/k_V)^R)`, which is `3.87` at `t = 2` and `7.91` at `t = 3`.
- So the whole deficit sits in `E d - E r > 0`.

In any group with `F_2[K]` directly finite, Theorem 3 gives `E d <= 1` for this code on every
pattern. So:
- the loop escapes exactly at step 1 of Theorem 3, where there is no associative ring in which
  `c(fe) = (cf)e`;
- Theorem C of the firewall kills one gadget pattern without direct finiteness. The left inverse
  `c_1(1 + δ + δ²)` of `Ê` is a right zero divisor, which is impossible for a left inverse:
  `b a = 0` implies `b = b a Ê = 0`;
- Theorem 3 is the quantitative version on every pattern, and it names direct finiteness as the
  invariant.

## 6. Where the method stops

**6.1. General gated linear codes (RELD).** Let `L_j` be arbitrary: it mixes coordinates, or outputs
several functionals on one coordinate. Recovering `λ ∈ F_q^{k_V}` at site 1 means

    λ = Σ_f μ_f f L_{J_f}   (rows over F_q[G]) ,

a left inverse of a column over `F_q[G]`. Such inverses are not unique even over commutative rings.
For example, with `T^{(1)} = T^{(2)} = 1`, `a_1 + a_2 = 1` has many solutions. So step 1 of Theorem 3
has no analogue.

Even for a fixed invertible matrix `T` gated by rows, with `M_n(F_q[K])` directly finite, the
recovered space `Λ` satisfies `λ T^{-1}(g) ∈ F_q^{I_{J_g}}` for all `g`. Turning these pointwise
support constraints into `dim Λ <= E |I_{J_1}|` needs a translation-invariant dimension.
- The natural substitute is `id_Λ = Σ_g (Λ -> F_q^{I_{J_g}} -> Λ)`, which comes from
  `T^{-1} T = 1`.
- Its trace only gives `dim Λ` mod `p`.
- In characteristic 0 a von Neumann trace would do this. Over `F_q` it needs a Sylvester rank
  function on the crossed product `C(Jset^G, F_q) ⋊ G` that is compatible with the counting. That is
  linear-sofic-type data.

**Proposition 8 (RELD over finite groups).** If `G` is finite and `W ⊆ G`, then
`E d(J_F) <= E r(J_1)` for every pointer-linear code.

*Proof.*
- Fix all pointers. Let `L_all` be the map `v -> (Z_g)_{g ∈ G}`, of rank at most `Σ_g r(J_g)`.
- The spaces `U_g = row L_all ∩ span v(g)` lie in independent coordinate blocks, so
  `Σ_g dim U_g <= rk L_all`.
- `d_g <= dim U_g`, because the codewords `gF` form a sub-collection.
- Take expectations and use translation invariance: `|G| E d <= |G| E r`. QED

The same count along sofic models should give RELD on sofic groups. That is not claimed here, since
those groups are already Rokhlin-maximal. The OPEN statement for all groups is the node
`pointer-gated-linear-codes-are-rank-dominated`.

**6.2. Non-monomial routing.** Suppose `T_i^{(j)} = u_j T_i` with `u_j` a non-trivial unit. Then
uniqueness still fixes `Σ_j a_j u_j = T_i^{-1}`, but step 2 (support) fails, because `a_j` is no
longer read off the support of `T_i^{-1}`.

**6.3. Nonlinear value part.** Theorem 1 needs linearity in `v`. A witness that survives both
Theorem 3 and Proposition 5 must do one of these:
- mix value coordinates through the pointer (Section 6.1);
- route through non-trivial units;
- have a pointer that is not abelian homomorphic and is itself a witness, which is Corollary 2 on
  fewer coordinates;
- be nonlinear in every split of the coordinates.

## 7. Recipe condition on non-directly-finite groups

By Corollary 4, a gated monomial-diagonal witness with a dominated pointer needs `T ∈ F_q[K]`,
`supp T ⊆ E`, with `a T = 1 != T a`. It also needs the random sets
`S = {f h_{J_f} : i ∈ I_{J_f}}` to contain the support of some left inverse
`a + b(1 - T a)` with probability above the density `P(i ∈ I_{J_1})`. The support of such a left
inverse must then be sparse relative to that density. By Corollary 6 this recipe cannot give a new
non-maximal group, since every such host already has `rho_{q'} = 0`. It could still be a
constructive way to exhibit collapse, for example on a Kaplansky counterexample.
