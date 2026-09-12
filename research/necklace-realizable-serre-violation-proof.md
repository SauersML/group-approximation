---
rg: 2
id: necklace-realizable-serre-violation-proof
kind: route
title: Count primitive closed walks and inject the six-letter Z^3 walk into the eight-letter walk by an injective endomorphism
target: necklace-realizable-measures-can-violate-serre
requires:
  - euler-integral-measure-violates-serre-inequality
---

Notation as in the claim. Write `S_sigma = {±e_1, ±e_2, ±e_3}` and
`S_nu = {(±1,±1,±1)}` in additive notation for `Z^3`, so that
`T_sigma = sum_(s in S_sigma) s` and `T_nu = sum_(s in S_nu) s` in `Z[Z^3]`.

**1. Nonnegative matrices over torsion-free groups have realizable moments.**
Let `G` be torsion-free and `S in M_k(Z_(>=0)[G])`.
- *Letters.* A letter is `(a, b, g, c)` with `1 <= c <= S_ab(g)`. It goes from
  vertex `a` to vertex `b` with value `g`.
- *Closed words.* A word `l_1 ... l_j` is closed if consecutive letters chain
  (the end of `l_i` is the start of `l_(i+1)`, and the end of `l_j` is the start
  of `l_1`) and the product of the values is `e`. Expanding the entries of
  `S^j` gives `Tr tau(S^j) = #X_j`, where `X_j` is the set of closed words of
  length `j`.
- *Rotation.* Rotation maps `X_j` to itself: vertex closure is cyclic, and the
  product is conjugated.
- *Primitive roots.* Every word is `u^m` for a unique primitive word `u` of
  length `d = j/m`. If `u^m` is closed, then `u` chains back to its own start,
  since letter `d+1` equals letter `1`. Also `value(u)^m = e`, so
  `value(u) = e` because `G` is torsion-free. Conversely `u^m` is closed when
  `u` is.
- *Counting.* Primitive words have rotation orbits of size exactly `d`. So
  `#X_j = sum_(d | j) d * p_d`, where `p_d` is the number of rotation orbits of
  primitive closed words of length `d`. Möbius inversion recovers these `p_d`
  from `(#X_j)`, so `(Tr tau(S^j))_j` is realizable.

Weights are split into copies instead of carried as in
`torsion-free-integral-zeta-is-an-integer-euler-product`, which is why the
exponents come out nonnegative.

**2. An injective endomorphism of Z^3 carries sigma's letters into nu's.**
Let `phi : Z^3 -> Z^3` be the homomorphism with
`phi(e_1) = (1,1,1)`, `phi(e_2) = (1,-1,-1)`, `phi(e_3) = (-1,1,-1)`.
- *Injective.* The matrix with these columns has determinant `4`, so `phi` is
  injective.
- *Letters.* `phi` maps `S_sigma` bijectively onto the six elements
  `±(1,1,1), ±(1,-1,-1), ±(-1,1,-1)` of `S_nu`.

Fix `P in M_k(Z_(>=0)[x])` with entries `P_ab(x) = sum_r q_(ab,r) x^r`.
- *Letters of `P(T)`.* Its letters are `(a, b, r, c, w)` with
  `1 <= c <= q_(ab,r)` and `w in S^r`, of value `sum(w)`. Here `S` is `S_sigma`
  for `T_sigma` and `S_nu` for `T_nu`, and `r = 0` is the empty word, of value
  `0`.
- *Counting.* Expanding `P(T)^j` shows that `Tr tau(P(T)^j)` is the number of
  closed words over these letters, exactly as in step 1, with `G = Z^3`.
- *The map.* Define `Phi(a, b, r, c, w) = (a, b, r, c, phi(w))`, letterwise on
  `w`. It is injective on letters, and `value(Phi(l)) = phi(value(l))`.
- *Words.* Extended letterwise to words, `Phi` is injective, commutes with
  rotation, and preserves chaining. It preserves "value `0`" in both directions
  because `phi` is an injective homomorphism. So it maps closed words to closed
  words injectively and rotation orbits to rotation orbits.
- *Primitivity.* Since `Phi` is injective and rotation-equivariant, it preserves
  rotation stabilizers, so primitive words go to primitive words.
- *Conclusion.* `p_d(P(T_sigma)) <= p_d(P(T_nu))` for every `d`.

**3. The images of mu are realizable.**
For self-adjoint `T`, `integral Tr(P(x)^j) d mu_T = Tr tau(P(T)^j)`, since the
entries of `P(T)` are polynomials in `T`. Hence, with
`N_j = integral Tr(P(x)^j) d mu`,

```text
N_j = 23 * Tr tau(P(T_nu)^j) - Tr tau(P(T_sigma)^j)
    = sum_(d | j) d * ( 23 p_d(P(T_nu)) - p_d(P(T_sigma)) ).
```

- The bracket is an integer, and by step 2 it is at least `22 p_d(P(T_nu)) >= 0`.
- By uniqueness of Möbius inversion, the bracket is the necklace number of
  `(N_j)`.
So `(N_j)` is realizable for every `k` and every `P`, and `mu` is necklace
realizable.

**4. Positivity and the log integral.**
- *Positivity.* `euler-integral-measure-violates-serre-inequality` shows that
  `mu` is a positive measure of mass `22`. So
  `integral P^* P d mu >= 0` for every `P in M_k(C[x])`, i.e. the moment
  functional is completely positive.
- *Log integral.* The same claim gives
  `integral_(x != 0) log|x| d mu = -m(x+1/x+y+1/y+z+1/z) < 0`.

**5. Spectral measures of nonnegative elements.**
Step 1 with `S = P(T)` shows that the spectral measure of every self-adjoint
`T in M_n(Z_(>=0)[G])` over a torsion-free `G` is necklace realizable:
`P(T) in M_(kn)(Z_(>=0)[G])` for `P in M_k(Z_(>=0)[x])`.

This completes the proof.
