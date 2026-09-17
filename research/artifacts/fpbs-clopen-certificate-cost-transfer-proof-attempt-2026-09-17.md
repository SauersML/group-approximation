# Generator repair edges on the no-path sets, Borel pieces by group element, clopen regularity and cylinder total variation

*Attempt artifact (2026-09-17), formerly route `fpbs-clopen-certificate-cost-transfer-proof` into `fpbs-clopen-certificate-cost-transfer`, requires []. Demoted from the graph because the referee vote of lens 1 was lost for this result; lenses 2 and 3 returned *survives*. No mathematical error has been reported. Restore it as a route once a full referee pass survives.*

Full written proof. No imported theorem is used beyond the definition of cost and regularity of
Borel probability measures on the compact zero-dimensional space `L^G`.

**Item 1.** Consider the graphing with pieces `gamma_i|A_i` (`i <= M`) and `s|N_s(Phi, l)`
(`s ∈ S`). Its cost is `c_l(Phi, nu)`. Fix `x` and `s ∈ S`. If `x ∈ N_s` the piece `s|N_s`
joins `x` to `s.x`. Otherwise there is a `Phi`-path from `x` of product `s`, and it ends at
`s.x`. So every point is joined to all its `S`-neighbours. Since `S` generates `G`, the graphing
generates the orbit relation, and `C(nu) <= c_l(Phi, nu)`. Freeness is not used.

**Item 2.** By item 1 it suffices to show `inf c_l <= C(nu)`. Assume `C(nu) < ∞`, fix `eps > 0`,
and take a Borel graphing `(phi_k: D'_k -> R'_k)_k` generating the orbit relation with cost
`< C(nu) + eps`. Split `D'_k` into the Borel sets `{x : phi_k(x) = gamma.x}`, `gamma ∈ G`. Since
`nu` is essentially free these sets cover `D'_k` up to a null set, and restricting to a conull
invariant Borel set where the action is free they are disjoint. This gives a countable list of
pieces `(gamma_j, D_j)` with `sum_j nu(D_j) < C(nu) + eps` that still generates.

For `N, l` let `E_s(N, l)` be the set of `x` with no path of length `<= l` using the first `N`
pieces and with product `s`. These sets decrease as `N` and `l` grow. For almost every `x` there
is a finite path of the full graphing from `x` to `s.x`. It uses finitely many pieces, and by
freeness its product is `s`. So `nu(E_s(N, l)) -> 0`. Choose `N, l` with
`sum_s nu(E_s(N, l)) < eps`.

Let `r = max_{j <= N} |gamma_j|`. The clopen sets form an algebra generating the Borel
σ-algebra, so for `theta > 0` there are clopen `A_j` with `nu(A_j Δ D_j) < theta`, `j <= N`. Put
`Phi = ((gamma_j, A_j))_{j <= N}`. Whether `x ∈ N_s(Phi, l)` versus `x ∈ E_s(N, l)` depends only
on which of the sets `A_j` or `D_j` contain the points `g.x`, `g ∈ B_{lr}`. So the two events
differ only on the union over `g ∈ B_{lr}` and `j <= N` of `g^{-1}(A_j Δ D_j)`. By invariance
this has measure at most `|B_{lr}| N theta`. Therefore

`c_l(Phi, nu) <= C(nu) + eps + N theta + eps + |S| |B_{lr}| N theta`,

and choosing `theta` small gives `c_l(Phi, nu) < C(nu) + 3 eps`.

**Item 3.** `c_l(Phi, .)` is a sum of `M + |S|` measures of cylinder events over `W`. Each
changes by at most `TV_W(nu, nu')`. Combine this with item 1 for `nu'`.
