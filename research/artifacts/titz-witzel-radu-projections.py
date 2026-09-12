"""Radu BMW lattice Gamma_R = <a,b,c,x,y,z | a2,b2,c2,x2,y2,z2, axax, ayay, azbz,
bxbx, bycy, cxcz> (Titz Mite--Witzel Prop 3.4(1)).  Compute the two projection
vertex groups:

  G_h = image of V=<x,y,z> acting on reduced words over {a,b,c}  (tree T_h),
  G_v = image of A=<a,b,c> acting on reduced words over {x,y,z}  (tree T_v).

Square rule: for horizontal h and vertical v, h v = v' h' with (v',h') = T[(h,v)].
Inverting (all generators are involutions): v h = h' v'.
  * vertical state v reading horizontal letter h outputs h', next state v'.
  * horizontal state h reading vertical letter v outputs v', next state h'.
"""
import itertools, sys, math, collections

T = {('a','x'):('x','a'), ('a','y'):('y','a'), ('a','z'):('z','b'),
     ('b','x'):('x','b'), ('b','y'):('y','c'), ('b','z'):('z','a'),
     ('c','x'):('z','c'), ('c','y'):('y','b'), ('c','z'):('x','c')}

# sanity: the six relators hold as corner identities
def check_table():
    # axax: a x = x a ; ayay ; azbz: a z = z b ; bxbx ; bycy: b y = y c ; cxcz: c x = z c
    assert T[('a','x')] == ('x','a')
    assert T[('a','y')] == ('y','a')
    assert T[('a','z')] == ('z','b')
    assert T[('b','x')] == ('x','b')
    assert T[('b','y')] == ('y','c')
    assert T[('c','x')] == ('z','c')
    # completeness / bijectivity (bireversibility)
    assert len(set(T.values())) == 9
check_table()

def act_h(state, word):
    """vertical state acting on horizontal word"""
    out = []
    v = state
    for h in word:
        v2, h2 = T[(h, v)]
        out.append(h2)
        v = v2
    return tuple(out)

def act_v(state, word):
    """horizontal state acting on vertical word"""
    out = []
    h = state
    for v in word:
        v2, h2 = T[(h, v)]
        out.append(v2)
        h = h2
    return tuple(out)

def reduced_words(alpha, n):
    words = [()]
    for _ in range(n):
        new = []
        for w in words:
            for s in alpha:
                if not w or w[-1] != s:
                    new.append(w + (s,))
        words = new
    return words

def perm_on_level(actfn, gens, alpha, n):
    words = reduced_words(alpha, n)
    idx = {w: i for i, w in enumerate(words)}
    perms = {}
    for g in gens:
        p = [idx[actfn(g, w)] for w in words]
        perms[g] = p
    return words, perms

def compose(p, q):  # (p*q)(i) = p(q(i))  apply q first
    return [p[i] for i in q]

def word_perm(perms, word, n_points):
    # word applied right-to-left as group element g1 g2 ... gk acting on the left: rightmost first
    p = list(range(n_points))
    for g in word:          # g1 g2 ... : leftmost is applied last
        p = compose(p, perms[g])
    return p

def perm_order(p):
    seen = [False]*len(p); order = 1
    for i in range(len(p)):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            order = order * L // math.gcd(order, L)
    return order

def is_identity(p):
    return all(i == j for i, j in enumerate(p))

def group_order(perms, npts):
    try:
        from sympy.combinatorics import Permutation, PermutationGroup
    except Exception:
        return None
    G = PermutationGroup([Permutation(p) for p in perms.values()])
    return G.order()

def reduced_gen_words(gens, L):
    out = []
    for n in range(1, L+1):
        out.extend(reduced_words(gens, n))
    return out

def analyse(name, actfn, gens, alpha, levels, rel_level, rel_len):
    print(f"==== {name}: generators {gens} acting on reduced words over {alpha}")
    for n in levels:
        words, perms = perm_on_level(actfn, gens, alpha, n)
        npts = len(words)
        order = group_order(perms, npts) if n <= 8 else None
        lg = (math.log2(order) if order else None)
        # element orders of products of two/three distinct generators
        eo = {}
        for w in [gens[:2], gens[1:3], (gens[0], gens[2]), gens]:
            eo[''.join(w)] = perm_order(word_perm(perms, w, npts))
        print(f"level {n}: points {npts}, |G_n| = {order} (log2 {lg}), orders {eo}")
        sys.stdout.flush()
    # short relations: reduced generator words acting trivially on level rel_level
    words, perms = perm_on_level(actfn, gens, alpha, rel_level)
    npts = len(words)
    rels = []
    for w in reduced_gen_words(gens, rel_len):
        if is_identity(word_perm(perms, w, npts)):
            rels.append(''.join(w))
    print(f"reduced generator words of length <= {rel_len} trivial on level {rel_level}: {len(rels)}")
    print(' '.join(rels[:80]))
    sys.stdout.flush()

if __name__ == '__main__':
    levels = list(range(1, 11))
    analyse('G_h = pr_h(V)', act_h, ('x','y','z'), ('a','b','c'), levels, 10, 10)
    analyse('G_v = pr_v(A)', act_v, ('a','b','c'), ('x','y','z'), levels, 10, 10)
