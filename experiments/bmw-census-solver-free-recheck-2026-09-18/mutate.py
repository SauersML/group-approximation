# Non-vacuity of recheck.py: corrupt valid certificates in several ways and require every corruption rejected.
#   usage: python3 mutate.py ROOT [ROOT2 ...]
import sys, copy, json
import recheck as R
R.ROOTS = sys.argv[1:] or ['.']
certs = {}
for pat, c, kind, src, pay in R.certificates():
    certs.setdefault(kind, []).append((pat, c, pay))
fails = 0
def expect_bad(name, fn):
    global fails
    try:
        fn(); print('NOT REJECTED:', name); fails += 1
    except (R.Bad, KeyError, AssertionError, IndexError) as e:
        print('rejected: %-44s (%s)' % (name, str(e)[:60]))

# (1) chains: the Klein chain of 40_40 #281, and the power chain of 50_30 #470
for pat, c, pay in certs['chain']:
    if (pat, c) == ('40_40', 281):
        G = R.load_class(pat, c); xs = [R.parse_bar(w) for w in pay]
        R.check_chain(G, xs)
        expect_bad('chain: one element replaced', lambda: R.check_chain(G, [xs[0], xs[2], xs[1], xs[3]]))
        expect_bad('chain: element outside Gamma^+', lambda: R.check_chain(G, [xs[0] + (('v', 0),)] + xs[1:]))
        expect_bad('chain: dropped element', lambda: R.check_chain(G, xs[:3]))
    if (pat, c) == ('50_30', 470):
        G = R.load_class(pat, c); xs = [R.parse_bar(w) for w in pay['chain']]
        roots = {k: R.parse_bar(w) for k, w in pay['roots'].items()}
        R.check_chain(G, xs, roots)
        expect_bad('power chain: power step reversed', lambda: R.check_chain(G, [xs[1], xs[0]] + xs[2:], roots))
        expect_bad('power chain: no (K) step', lambda: R.check_chain(G, [xs[0], xs[1]], roots))
# (2) a cone tree of w10
pat, c, T = next(x for x in certs['tree'] if x[0] == '30_30' and x[1] == 10)
G = R.load_class(pat, c); R.check_tree(G, T, R.parse_lp)
def leaf(t):
    while t[0] == 'split': t = t[2]
    return t
t1 = copy.deepcopy(T); leaf(t1)[2].pop(0)
expect_bad('tree: dropped first leaf step', lambda: R.check_tree(G, t1, R.parse_lp))
t2 = copy.deepcopy(T); leaf(t2)[2][0][0] = leaf(t2)[2][0][2] + leaf(t2)[2][0][1]
expect_bad('tree: wrong product (w u for u w)', lambda: R.check_tree(G, t2, R.parse_lp))
t3 = copy.deepcopy(T); lf = leaf(t3); lf[1] = [lf[1][0], lf[1][0]]
expect_bad('tree: leaf without contradiction', lambda: R.check_tree(G, t3, R.parse_lp))
t4 = copy.deepcopy(T); t4[1] = t4[1] + 'v0'
expect_bad('tree: split outside Gamma^+', lambda: R.check_tree(G, t4, R.parse_lp))
# (3) a lemma certificate of w11
pat, c, rec = certs['lemmas'][0]
G = R.load_class(pat, c); R.check_lemmas(G, rec)
m1 = copy.deepcopy(rec); m1['lemmas'][0]['steps'].pop()
expect_bad('lemmas: dropped last step of lemma 0', lambda: R.check_lemmas(G, m1))
m2 = copy.deepcopy(rec); m2['lemmas'][-1]['S'] = [0]
expect_bad('lemmas: nonempty last lemma', lambda: R.check_lemmas(G, m2))
m3 = copy.deepcopy(rec); m3['els'][0] = m3['els'][0] + 'v0'
expect_bad('lemmas: table entry outside Gamma^+', lambda: R.check_lemmas(G, m3))
m4 = copy.deepcopy(rec)
for i, L in enumerate(m4['lemmas']):
    ls = [s for s in L['steps'] if s[0] == 'L']
    if ls: ls[0][1] = i; break
expect_bad('lemmas: L-step citing its own lemma', lambda: R.check_lemmas(G, m4))
m5 = copy.deepcopy(rec); e = m5['lemmas'][0]['end']; m5['lemmas'][0]['end'] = [e[0], e[0]]
expect_bad('lemmas: end without contradiction', lambda: R.check_lemmas(G, m5))
m6 = copy.deepcopy(rec)
for L in m6['lemmas']:
    ps = [s for s in L['steps'] if s[0] not in ('sq', 'L')]
    if ps: ps[0][1], ps[0][2] = ps[0][2], ps[0][1]; break
expect_bad('lemmas: product factors swapped', lambda: R.check_lemmas(G, m6))
print('summary: %d corruptions not rejected' % fails)
