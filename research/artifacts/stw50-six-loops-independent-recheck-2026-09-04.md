# Independent recheck of the STW L six-loop construction

Second-reader audit of
`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`, performed
2026-09-04 from the manuscript's own definitions, without consulting its
certificate script and before seeing the `stw50-*` nodes.  Its closing
paragraph records that the construction "has not undergone independent
expert review"; this is a partial answer to that, by a second reader
rather than an expert.

**Verdict: every finite step reproduces.  No discrepancy found.**

Recomputed and confirmed:

* `M(u)_{ij} = delta_{ij} + u_j` gives `(I - M^t)_{ij} = -u_i`, so
  `I - M^t = -u 1^t`, `K_0 = Z^n/Z u`, `K_1 = {x : sum x_i = 0}` -- and
  the two matrices `[[2,1,2],[1,2,2],[1,1,3]]`, `[[2,2],[1,3]]` are what
  `u = (1,1,2)` and `u = (1,2)` produce.
* `det((1,1,2),(1,1,1),(1,0,0)) = -1` (expand along the third column:
  `+det[[1,1],[2,1]] = -1`), so `{e_C, b}` is a basis of `K_0(C)`; and
  `2e_C - b - [p_2] = u`, `-e_C - [p_3] = -u`, giving (7).  For `B`,
  `(x,y) |-> 2x - y` has kernel `Z(1,2)` and sends `e_B, [p], [q]` to
  `1, 2, -1`, giving (9).
* Row relations: the edge entries of `R_i` are exactly the edges out of
  `i` (the `a_{ij}^{(k)}` plus `d_i`), so they sum to `p_i` and the
  remaining columns add `p_j` for `j != i` -- `R_i R_i^* = 1`.  Every
  column `(j,k)` has initial projection `p_j` regardless of `i`, and the
  three off-diagonal cases vanish (edge relation, vertex orthogonality,
  and `p_j s_a = p_j p_i s_a = 0` in the mixed case) -- `R_i^* R_i = P`.
  Hence `W_i W_i^* = R_i P R_i^* = 1`.
* Equation (4): `i < n` keeps the rescaled edge out of `R_n`, so
  `g(W_k)W_k^* = g(R_k)R_k^*`, which corrects the sum `1` by
  `(z-1)s_a s_a^*` exactly when `k = i`.  Equation (5) then follows from
  `s_a s_a^* ~ s_a^* s_a = p_{r(a)}`.
* Integrality: `Delta_{g_{i3}}([U_k]) = -delta_{ik} e_C`, so minus the
  `e_C`-coordinate gives a left inverse to `Z^2 -> K_1(C)`; a rank-two
  summand of a rank-two free group is everything.  Same argument in rank
  one makes `[V]` a generator of `K_1(B)`.
* Both Koszul signs in section 5, the whole of `L`, `det L = 1` by the
  block triangular form with `[[0,-1],[1,0]]` in the corner, the inverse
  formula (16) (`c_1+c_5 = a`, `c_2 = b`, `c_3+c_6 = c`, `c_4 = d`,
  `-c_6 = f`, `c_5 = g`), and the four kernel columns (18) as
  col2, col4, col5-col1, col6-col3.

## The one import that carries real weight, cross-checked

Lemma 1 is the only step a second reader cannot recompute, and the
manuscript proves it from Dadarlat's Theorem 6.3.  It is corroborated
independently, without opening that paper, by the form STW themselves
quote in Problem L: `pi_k(Aut(A)) = KK^1(C_u A, S^k A)`.

For the mapping cone of the unital inclusion `C -> A`, the six-term
sequence gives `K_0(C_u A) = K_1(A)` (because `[1_A] : Z -> K_0(A)` is
injective, so `K_0(C_u A)` is the image of `K_1(A)`) and
`K_1(C_u A) = coker([1_A]) = K_0(A)/Z[1_A]`.  Since
`KK^1(-, SA) = KK^0(-, A)`, the UCT with vanishing `Ext` gives

```text
KK^1(C_u A, SA) = Hom(K_1(A), K_0(A)) (+) Hom(K_0(A)/Z[1_A], K_1(A)),
```

which is Lemma 1 on the nose, and has rank `4 + 2 = 6` when both
K-groups are `Z^2` -- the value STW state for `pi_1(Aut(A_theta))`.

The PARITY is corroborated a third time by the construction itself:
applying an automorphism loop to a unitary yields a loop of unitaries,
i.e. a `K_1 -> K_0` map.  So the parity-reversing reading is the right
one, and a parity-preserving misreading of Dadarlat (which would also
have given rank 6 here, since `K_0` and `K_1` are both `Z^2`) is ruled
out by the actual computation rather than by rank counting.

## One simplification available in section 7

Section 7 takes the complement `q` and the retraction `r` from the
earlier rotation-retraction artifact.  It does not need to.  Given
Lemma 1, the two coordinates
`alpha |-> ((Delta_alpha x)_e, (Delta_alpha y)_e)` are already a
homomorphism `pi_1(Aut(D)) -> Z^2`, and columns 1 and 3 of `L` are the
first and third standard basis vectors, so the transported
`sigma_1, sigma_3` are a visible section of it and `ker r` is the
sublattice `a = c = 0`.  The four `kappa` columns have unimodular `4x4`
minor there.  So the kernel-basis assertion of
`stw50-explicit-basis-of-rotation-retraction-kernel` stands on the
six-loop node alone; the dependence on
`stw50-rotation-loops-form-a-direct-summand` in
`stw50-kirchberg-kernel-loops-proof` is a convenience, not a load-bearing
prerequisite.  This is an observation, not a defect: the route as written
is correct.

## Not checked here

Dadarlat's theorem as printed, unital Kirchberg--Phillips,
Bates--Pask--Raeburn--Szymanski, Kumjian--Pask, Drinen--Tomforde,
Rosenberg--Schochet, Kunneth, Pimsner--Voiculescu.  No source was opened
in this session; the cross-check above is internal.  Nothing here is
machine-checked, and this is not expert review.
