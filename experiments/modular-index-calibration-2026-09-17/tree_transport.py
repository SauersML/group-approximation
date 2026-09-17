#!/usr/bin/env python3
"""Exact random-order decoder transport for automata on the 3-regular tree with a fixed end.

Lane (c) of notes/agent-coordination-playbook-2026-09-17.md, Section 11: is the transport ratio 2 of the
end-fixing tree automaton an index of strictness, or the modular correction of the host?

Vertices near the root o are encoded canonically as (k, s): go up k steps from o to the ancestor a_k, then
down along the bit string s.  o is always the 0-child of its parent, so (k, '0'+t) with k >= 1 is (k-1, t).

For an automaton y = kappa(x) with equivariant decoder memory D(u) (a Stab(u)-invariant finite set of
output sites from which x(u) is a function), and an i.i.d. uniform order U,

    t(u, w) = I( x(u) ; y(w) | y(D(u) ∩ past(w)), U ),     w in D(u).

out(o)          = sum_{w in D(o)} t(o, w)                    (= log |A_in| by the chain rule)
in(o)           = sum_{u : o in D(u)} t(u, o)                 (unweighted; equals out on a group)
in_weighted(o)  = sum_{u : o in D(u)} t(u, o) * 2^(b - a)     (u -> o goes up a steps and down b steps)

The weighted mass-transport principle for Aut(T, xi) (proved in the research artifact by counting orbit
sizes) says in_weighted = out for every invariant transport.  This script verifies that numerically and
prints the unweighted ratio out/in, the site entropy H(y(o)), and both domination inequalities.
The in-terms t(u, o) are computed directly at each contributing u, so in_weighted = out is a real check.

All logs are base 2.  Exact enumeration of the finitely many input symbols the terms depend on.
"""
import itertools
import math
from collections import defaultdict


# ---------------------------------------------------------------- tree coordinates
def canon(v):
    k, s = v
    while k >= 1 and s.startswith('0'):
        k, s = k - 1, s[1:]
    return (k, s)


def parent(v):
    k, s = canon(v)
    if s:
        return canon((k, s[:-1]))
    return (k + 1, '')


def children(v):
    k, s = canon(v)
    return [canon((k, s + '0')), canon((k, s + '1'))]


def sibling(v):
    p = parent(v)
    c0, c1 = children(p)
    v = canon(v)
    return c1 if v == c0 else c0


def height_type(u, o):
    """(a, b): from u go up a steps to the meet, then down b steps to o."""
    anc_u = [canon(u)]
    for _ in range(40):
        anc_u.append(parent(anc_u[-1]))
    anc_o = [canon(o)]
    for _ in range(40):
        anc_o.append(parent(anc_o[-1]))
    for a, x in enumerate(anc_u):
        if x in anc_o:
            return a, anc_o.index(x)
    raise ValueError


# ---------------------------------------------------------------- information theory
def H(dist):
    return -sum(p * math.log2(p) for p in dist.values() if p > 0)


def mutual_info_cond(samples, fx, fy, fz):
    """I(X; Y | Z) under the uniform law on `samples`."""
    n = len(samples)
    j = defaultdict(float)
    xz = defaultdict(float)
    yz = defaultdict(float)
    z = defaultdict(float)
    for s in samples:
        X, Y, Z = fx(s), fy(s), fz(s)
        j[(X, Y, Z)] += 1 / n
        xz[(X, Z)] += 1 / n
        yz[(Y, Z)] += 1 / n
        z[Z] += 1 / n
    return H(xz) + H(yz) - H(j) - H(z)


# ---------------------------------------------------------------- automata
class Automaton:
    """rule(xget, v) -> output symbol, where xget(site) returns the input symbol at a site.
    inputs: list of input alphabets per track (the input symbol at a site is a tuple over tracks).
    deps(v): sites of x that y(v) reads.  decoder memory D(o): list of sites relative to o."""

    def __init__(self, name, tracks, rule, deps, memory, decode):
        self.name, self.tracks, self.rule, self.deps = name, tracks, rule, deps
        self.memory = memory
        self.decode = decode  # decode(yget, u) -> x(u); used to check the decoder

    def symbols(self):
        return list(itertools.product(*[range(q) for q in self.tracks]))


def ball(radius):
    o = (0, '')
    seen = {o}
    frontier = [o]
    for _ in range(radius):
        nxt = []
        for v in frontier:
            for w in [parent(v)] + children(v):
                w = canon(w)
                if w not in seen:
                    seen.add(w)
                    nxt.append(w)
        frontier = nxt
    return seen


def term_table(aut, u):
    """t(u, w) for every w in D(u), by exact enumeration."""
    u = canon(u)
    D = [canon(w) for w in aut.memory(u)]
    sites = set([u])
    for w in D:
        sites.update(canon(s) for s in aut.deps(w))
    sites = sorted(sites)
    syms = aut.symbols()
    samples = list(itertools.product(syms, repeat=len(sites)))
    idx = {s: i for i, s in enumerate(sites)}

    def y(sample, w):
        return aut.rule(lambda site: sample[idx[canon(site)]], w)

    for smp in samples:  # the decoder really decodes x(u) on this window
        assert aut.decode(lambda site, smp=smp: y(smp, canon(site)), u) == smp[idx[u]], aut.name
    m = len(D)
    terms = {}
    for w in D:
        others = [v for v in D if v != w]
        t = 0.0
        for r in range(len(others) + 1):
            prob = math.factorial(r) * math.factorial(m - 1 - r) / math.factorial(m)
            for S in itertools.combinations(others, r):
                t += prob * mutual_info_cond(samples,
                                             lambda s: s[idx[u]],
                                             lambda s, w=w: y(s, w),
                                             lambda s, S=S: tuple(y(s, v) for v in S))
        terms[w] = t
    return terms


def transport(aut, radius=3):
    o = (0, '')
    out_terms = term_table(aut, o)
    out = sum(out_terms.values())
    # in-mass at o: compute t(u, o) directly for every u near o with o in D(u)
    tin = 0.0
    tin_w = 0.0
    contributors = {}
    for u in ball(radius):
        D = [canon(w) for w in aut.memory(u)]
        if o not in D:
            continue
        t = term_table(aut, u)[o]
        a, b = height_type(u, o)
        contributors[str(u)] = (a, b, round(t, 6))
        tin += t
        tin_w += t * 2.0 ** (b - a)
    law = defaultdict(float)
    sites = sorted(set(canon(s) for s in aut.deps(o)))
    idx = {s: i for i, s in enumerate(sites)}
    samples = list(itertools.product(aut.symbols(), repeat=len(sites)))
    for smp in samples:
        law[aut.rule(lambda site, smp=smp: smp[idx[canon(site)]], o)] += 1 / len(samples)
    Hy = H(law)
    return dict(name=aut.name, log_in_alphabet=sum(math.log2(q) for q in aut.tracks), out=out, tin=tin,
                tin_weighted=tin_w, ratio_out_over_in=out / tin if tin else float('inf'), H_site=Hy,
                unweighted_domination=tin <= Hy + 1e-9, weighted_domination=tin_w <= Hy + 1e-9,
                out_terms={str(k): round(v, 6) for k, v in out_terms.items()}, in_terms=contributors)


def automata(q=2):
    P, C, S = parent, children, sibling
    auts = []

    # 1. the strict end-fixing automaton: copy the parent, decode by min over the two children
    auts.append(Automaton(
        f'strict copy-parent tau (q={q})', [q],
        rule=lambda x, v: x(P(v)),
        deps=lambda v: [P(v)],
        memory=lambda u: C(u),
        decode=lambda y, u: min(y(C(u)[0]), y(C(u)[1]))))

    # 2. bijective, decoder reads the parent: (x1(v), x2(v) + x1(p v))
    auts.append(Automaton(
        f'bijective shear up (q={q})', [q, q],
        rule=lambda x, v: (x(v)[0], (x(v)[1] + x(P(v))[0]) % q),
        deps=lambda v: [v, P(v)],
        memory=lambda u: [u, P(u)],
        decode=lambda y, u: (y(u)[0], (y(u)[1] - y(P(u))[0]) % q)))

    # 3. bijective, decoder reads the children: (x1(v), x2(v) + x1(c) + x1(c'))
    auts.append(Automaton(
        f'bijective shear down (q={q})', [q, q],
        rule=lambda x, v: (x(v)[0], (x(v)[1] + x(C(v)[0])[0] + x(C(v)[1])[0]) % q),
        deps=lambda v: [v] + C(v),
        memory=lambda u: [u] + C(u),
        decode=lambda y, u: (y(u)[0], (y(u)[1] - y(C(u)[0])[0] - y(C(u)[1])[0]) % q)))

    # 4. identity
    auts.append(Automaton(
        f'identity (q={q})', [q],
        rule=lambda x, v: x(v), deps=lambda v: [v], memory=lambda u: [u], decode=lambda y, u: y(u)))

    # 5. the skewed injective automaton of finite-left-inverse-identity-does-not-force-balance
    def kappa(x, v):
        x0v, x0s = x(v)[0], x(S(v))[0]
        z = 0 if (x0v == 1 and x0s == 0) else x(P(v))[1]
        return (x0v, z)

    def kappa_dec(y, u):
        c0, c1 = C(u)
        if (y(c0)[0], y(c1)[0]) == (1, 0):
            return (y(u)[0], y(c1)[1])
        return (y(u)[0], y(c0)[1])

    auts.append(Automaton(
        f'skewed injective kappa (q={q})', [q, q], rule=kappa,
        deps=lambda v: [v, S(v), P(v)],
        memory=lambda u: [u] + C(u),
        decode=kappa_dec))

    # 6. a strict automaton with balanced unweighted transport: tau x (shear up) on A x A^2
    auts.append(Automaton(
        f'strict product tau x shear-up (q={q})', [q, q, q],
        rule=lambda x, v: (x(P(v))[0], x(v)[1], (x(v)[2] + x(P(v))[1]) % q),
        deps=lambda v: [v, P(v)],
        memory=lambda u: C(u) + [u, P(u)],
        decode=lambda y, u: (min(y(C(u)[0])[0], y(C(u)[1])[0]), y(u)[1], (y(u)[2] - y(P(u))[1]) % q)))
    return auts


if __name__ == '__main__':
    import json
    results = []
    for q in (2, 3):
        for aut in automata(q):
            if q == 3 and ('shear down' in aut.name or 'kappa' in aut.name or 'product' in aut.name):
                continue  # 9^7 and 9^5 sample spaces; the q = 2 cases carry the point
            r = transport(aut)
            results.append(r)
            print(json.dumps(r))
    for r in results:
        assert abs(r['out'] - r['log_in_alphabet']) < 1e-9, r['name']        # chain rule
        assert abs(r['tin_weighted'] - r['out']) < 1e-9, r['name']           # modular mass transport
    print('checks passed: out = log|A_in| and weighted in = out for every automaton')

    # balanced equivariant decoder of the strict automaton for q = 3: sigma(y)(w) = 2 (y(c) + y(c')) mod 3
    q = 3
    assert all((2 * (a + a)) % q == a for a in range(q))                     # decodes tau
    counts = [sum(1 for a in range(q) for b in range(q) if (2 * (a + b)) % q == s) for s in range(q)]
    assert counts == [q] * q                                                  # uniform push-forward
    print('q = 3: sigma(y)(w) = 2(y(c) + y(c\') ) mod 3 is a symmetric, balanced decoder of tau')
    # q even: a symmetric f with f(a, a) = a has |f^-1(a)| odd, so no balanced symmetric two-child decoder
    print('q even: every symmetric two-child decoder of tau is unbalanced (|f^-1(a)| = 1 + 2k is odd)')
