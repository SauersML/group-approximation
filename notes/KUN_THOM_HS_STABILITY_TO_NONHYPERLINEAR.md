# Hilbert--Schmidt stability of the Kun--Thom witness would give a nonhyperlinear group

Date: 2026-08-13

## Compact-image invisibility

Let \(\Gamma<G\) be infranormal and let \(t\in G\) satisfy
\(t\Gamma t^{-1}\leq\Gamma\).  Put

\[
 F=G*_{\Gamma}(\Gamma\times C_2),
\]

write \(v\) for the edge involution, and choose \(\gamma\in\Gamma\) such
that \(t^{-1}\gamma t\notin\Gamma\).  The Kun--Thom word is

\[
 w=[tvt^{-1},\gamma]\ne1.                            \tag{1}
\]

Every finite-dimensional unitary representation \(\rho:F\to U(d)\) kills
\(w\).  Indeed, in the compact closure of \(\rho(G)\), the closure
\(H=\overline{\rho(\Gamma)}\) is normal.  This is the recurrence argument
in `FALSE_COMPACT_BOGOLIUBOV_APPROXIMATION_FOR_KUN_THOM.md`.  Since
\(\rho(v)\) centralizes \(H\), and the centralizer of a normal subgroup is
normalized by the ambient group, \(\rho(tvt^{-1})\) also centralizes
\(H\), hence \(\rho(\gamma)\).  Thus \(\rho(w)=1\).

The same statement holds for the commuting-lamp Kun--Thom wreath group and
its standard commutator witness.

## Stability criterion

Suppose that \(F\) is flexibly Hilbert--Schmidt stable in a form applicable
to pointwise asymptotic representations of its (possibly infinite)
presentation.  Then \(F\) is not hyperlinear.

For if \(F\) were hyperlinear, lift a faithful tracial-ultraproduct
embedding to unitary maps \(\phi_n:F\to U(d_n)\).  Flexible stability would,
after \(o(d_n)\) padding, perturb them in normalized Hilbert--Schmidt norm
to honest finite-dimensional representations \(\rho_n\).  The preceding
paragraph gives \(\rho_n(w)=1\), and therefore \(\phi_n(w)\to1\) in
normalized Hilbert--Schmidt norm.  This contradicts faithfulness, since the
canonical group trace gives

\[
 \|u_w-1\|_2^2=2.                                    \tag{2}
\]

Thus either the free-lamp group or the commuting-lamp group would be an
explicit nonhyperlinear group once the corresponding local/flexible
Hilbert--Schmidt stability theorem is proved.

## Scope

This route is distinct from proving the Kun--Thom wreath group hyperlinear.
It uses compact-image invisibility plus stability to prove the opposite
conclusion.  Existing polynomial stability of the ordinary lamplighter
group does not supply the needed theorem: its tower argument uses the
amenable translation geometry of the regular \(\mathbb Z\)-action, whereas
the Kun--Thom coset action is precisely the nonsofic Kazhdan/infranormal
action.  No stability claim is made here.

