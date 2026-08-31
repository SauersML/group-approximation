---
rg: 2
id: strict-kazhdan-compressor-forces-non-rfd
kind: claim
title: A strict Kazhdan compressor leaves a nonzero projection invisible to every finite-dimensional representation
artifacts:
  - research/strict-kazhdan-compressor-kazhdan-projection-proof.md
distinct_from:
  commutant-no-growth: that proves equality of finite-dimensional bicommutants; this produces an explicit nonzero projection in the finite-dimensional radical of the full group C-star algebra.
  tfd-finite-corner-collapse-and-rfd-firewall: that combines property TFD with RFD to deduce property T; this uses ordinary property T plus one strict conjugate inclusion to refute RFD outright.
  kun-thom-actor-is-rf-but-neither-rfd-nor-llp: that imports non-RFD from an SL3(Z) subgroup of the full Laurent actor; this applies to every one-compressor ascending HNN host, even when no such arithmetic subgroup is present.
---

**ESTABLISHED RFD OBSTRUCTION.**

Let \(H\leq G\) have property \((T)\), and suppose that for some
\(t\in G\),
\[
                 K=tHt^{-1}<H.                           \tag{SKC1}
\]
Let \(p_H\in C^*_{\max}(H)\) be the Kazhdan projection: in every unitary
representation its image is the orthogonal projection onto the
\(H\)-invariant vectors.  View \(p=p_H\) inside \(C^*_{\max}(G)\), and put
\[
                 q=tpt^{-1}.                             \tag{SKC2}
\]
Then
\[
 \boxed{\quad e=q-p\text{ is a nonzero projection and }
        \pi(e)=0\text{ for every finite-dimensional }
        \pi:C^*_{\max}(G)\to M_n(\mathbb C).\quad}         \tag{SKC3}
\]
Consequently
\[
 e\in I_{\mathrm{fd}}(G):=
 \bigcap_{\dim\pi<\infty}\ker\pi,\qquad e\ne0,             \tag{SKC4}
\]
and hence
\[
 \boxed{\qquad C^*_{\max}(G)\text{ is not residually
 finite-dimensional.}\qquad}                              \tag{SKC5}
\]

The proof is the finite-rank obstruction in its sharpest form.  For any
unitary representation \(\sigma\) of \(G\),
\[
 \operatorname{Fix}_{\sigma}(H)\subseteq
 \operatorname{Fix}_{\sigma}(K),
\]
so \(\sigma(p)\leq\sigma(q)\).  Thus \(p\leq q\) in the full group
C-star algebra and \(e=q-p\) is a projection.  If \(\sigma\) is
finite-dimensional, \(q=\sigma(t)p\sigma(t)^*\) has the same rank as
\(p\); the inclusion forces equality, so \(\sigma(e)=0\).

The projection is nevertheless nonzero.  In the quasi-regular
representation on \(\ell^2(G/K)\), the vector \(\delta_K\) is fixed by
\(K\) but is not fixed by \(H\), because \(K<H\).  Therefore
\[
       \sigma(q)\delta_K=\delta_K,\qquad
       \sigma(p)\delta_K\ne\delta_K,                       \tag{SKC6}
\]
and \(\sigma(e)\delta_K\ne0\).

This theorem rules out the proposed LLP--RFD strict-compressor host before
any orbit-rank, finite-presentation, or action-soficity question is asked.
In particular, an ascending HNN extension
\[
 G=\langle H,t\mid tht^{-1}=\alpha(h)\ (h\in H)\rangle
\]
of an infinite Kazhdan group by a proper injective endomorphism
\(\alpha(H)<H\) never has RFD full group C-star algebra.  Property FD
and every stronger finite-dimensional Fell-density hypothesis fail as
well.

This does not say that \(G\) is not residually finite as a group.  The
witness \(e\) is a C-star-algebraic projection rather than a nonidentity
group element, so finite quotients may still separate all elements of
\(G\) while failing to separate \(C^*_{\max}(G)\).
