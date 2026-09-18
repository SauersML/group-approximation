# Decide finite-support corner equations by Tarski, then diagonalize the Lin-Mastel-Slofstra compiler against the search with Kleene's recursion theorem

*Attempt artifact (2026-09-17), formerly route `fixed-decidable-host-corner-models-miss-a-separated-bcs-proof` into `fixed-decidable-host-corner-models-miss-a-separated-bcs`, requires [lin-explicit-fixed-bcs-gap-via-generic-conversion, paddock-slofstra-bcs-forbidden-projection-dictionary, binary-leavitt-unit-word-problem-decidable, leavitt-corner-host-is-the-simple-leavitt-unit-group, nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear]. Demoted from the graph at landing because the swarm-0917 referee stage returned no votes for this established result (votes lost), so it has not survived review. Restore it as a route once a full referee pass survives.*

## Imports

- **(I1) Lin, arXiv:2510.07162, Definition 6.2, Section 6.3 and Corollary 6.10**
  (verbatim in the artifact). `k-CLMIPco` is coRE-complete under mapping
  reductions, with yes-instances `omega_co(G) = 1` and no-instances
  `omega_co(G) <= 1/2` among synchronous games, and non-halting is the
  complete coRE problem. This gives a computable `F |-> G_F` with
  `not halt(F) => omega_co(G_F) = 1` and `halt(F) => omega_co(G_F) <= 1/2`.
  Commuting correlation sets are closed, so value one is attained.
- **(I2) Mastel--Slofstra, Section 3** (as recorded in
  `lin-explicit-fixed-bcs-gap-via-generic-conversion` and its artifact). The
  one-hot / losing-pair BCS `B_G` has a perfect quantum, quantum-approximable
  or commuting strategy if and only if `G` does. The construction is
  computable in `G`.
- **(I3) Paddock--Slofstra dictionary**
  (`paddock-slofstra-bcs-forbidden-projection-dictionary`). Tracial states on
  `A(B)` are perfect commuting strategies; homomorphisms into `R^U` are
  perfect quantum-approximable strategies; unital finite-dimensional
  representations are perfect quantum strategies.
- **(I4) Tarski--Seidenberg.** The first-order theory of the real closed
  field `R` is decidable.
- **(I5) Kleene's recursion theorem.** For every total computable
  transformation `T` of machine indices there is `e` with `M_e` and
  `M_(T(e))` computing the same partial function; `e` is computable from an
  index of `T`.

## Step 1: (FH1), corner models are Sigma^0_1

Let `A(B)` have generators `x_v` and relations `x_v^* = x_v`, `x_v^2 = 1`,
`[x_u, x_v] = 0` for `u, v` in a common context, and one polynomial identity
`p_c(x_(V_c)) = 0` per context. A unital star homomorphism into `qC[Gamma]q`
is exactly a tuple `a_v in C[Gamma]` with

```text
q^* = q = q^2 != 0,   q a_v = a_v q = a_v,   a_v^* = a_v,   a_v^2 = q,
[a_u, a_v] = 0,       p_c(a_(V_c)) = 0 with the unit replaced by q.      (T1)
```

Fix a finite set `S` of words, closed under formal inversion, and require the
supports of `q` and all `a_v` to lie in `S`. The relations in `(T1)` have
bounded degree `d`. Using the word-problem algorithm, compute the partition of
the finitely many words of length at most `d` in `S` into group elements. Then
the coefficients of every side of `(T1)` are integer polynomials in the real
and imaginary parts of the unknown coefficients, and `(T1)` becomes an
existential sentence over `R` (`q != 0` is "some coordinate of `q` is
nonzero"). By (I4) it is decidable. Every corner model has finite supports, so
enumerating all `S` gives a `Sigma^0_1` procedure, uniform in `B`. For the
fixed projection, `q = P_z` has known coefficients and the sentence is the same
without the `q` unknowns.

For a recursively presented host with `z != 1` known, guess a partition of the
bounded words and verify each merge by enumerating consequences of the
relators. If the true partition is coarser than the verified one, each true
coefficient is a sum of verified-class coefficients, so every equation `= 0`
in `(T1)` still holds. `P_z != 0` holds by hypothesis, so a verified solution
is a real corner model. The predicate is again `Sigma^0_1`.

## Step 2: corner models give tracial states

If `q != 0` is a projection in `C[Gamma]`, then `tau(q) = ||q||_2^2 > 0` for the
canonical trace `tau`, and `tau(q . q)/tau(q)` is a tracial state on
`qC[Gamma]q`. Pulling it back along a unital star homomorphism gives a tracial
state on `A(B)`. By (I3) this is a perfect commuting strategy for `B`, and by
(I2) for the source game.

## Step 3: the fixed point (FH2)

Let `T(e)` be the index of the machine which:
1. computes `G_e = G_(M_e)` by (I1) and `B_e = B_(G_e)` by (I2);
2. dovetails two searches:
   - (a) the Step 1 search for a corner model of `B_e` in `Gamma`;
   - (b) for `d = 1, 2, ...`, the Tarski decision (I4) of "there is a
     `d`-dimensional tensor-product strategy for `G_e` with value `> 1/2`";
3. halts as soon as either search succeeds.

Let `M_dag = M_e` for a Kleene fixed point `e` of `T` (I5). Suppose `M_dag`
halts. Then `omega_co(G_dag) <= 1/2` by (I1).
- If search (a) succeeded, Step 2 gives a perfect commuting strategy for
  `G_dag`, so `omega_co(G_dag) = 1`. Contradiction.
- If search (b) succeeded, `omega_co(G_dag) >= omega_q(G_dag) > 1/2`.
  Contradiction.

So `M_dag` does not halt. By (I1), `omega_co(G_dag) = 1`. By (I2) and (I3),
`A(B_dag)` has a tracial state. Since neither search ever succeeds,
`omega_q(G_dag) <= 1/2`, and `B_dag` has no corner model in `Gamma`.

A unital finite-dimensional representation of `A(B_dag)` would give, by (I3)
and (I2), a perfect quantum strategy for `G_dag`. A Connes-embeddable trace
would give a perfect quantum-approximable strategy, hence
`omega_q(G_dag) = 1`, since `omega_qa` is the closure of the finite-dimensional
values. Both contradict `omega_q(G_dag) <= 1/2`.

For a uniformly computable sequence of hosts, search (a) dovetails over all of
them. For a recursively presented host with `z != 1`, it uses the Step 1
variant. The argument is unchanged. For `Gamma = Delta`, decidability is
`binary-leavitt-unit-word-problem-decidable` transported along
`Delta ~= R^x` (`leavitt-corner-host-is-the-simple-leavitt-unit-group`). The
recursively presented variant also applies directly to the finite presentation
of `St_20(R)`, with `z = x_13(s_1t_1) != 1` from the same identification.

## Step 4: (FH3)

Each listed statement, applied to `M_dag` or `B_dag`, would give a corner
model of `B_dag` in `Gamma`, contradicting Step 3. For the procedure version:
the argument of Step 3 is itself a proof that `M_dag` does not halt, so the
procedure would have to output corner data for `B_dag`, which Step 1 would
then verify.

## Scope

Nothing here decides `LNC3` for `B_loop`. The loop source is non-halting for
a syntactic reason and is not built to diagonalize against any search. The
content is the kill: a proof of `LNC3` must use properties of `B_loop` that
`B_dag` does not share.
