# Non-vacuity test of verify_lemmas.py: the first certificate of the file must pass, and six
# corruptions of it must be rejected.  usage: mutate_lemmas.py certs.jsonl[.gz]
import sys, json, copy, gzip
from verify_lemmas import check
cert = json.loads((gzip.open if sys.argv[1].endswith('.gz') else open)(sys.argv[1], 'rt').readline())
print('original:', cert['pat'], cert['cls'], 'accepted', check(cert))
Lm = cert['lemmas']
i = next(k for k, L in enumerate(Lm) if any(s[0] not in ('L', 'sq') for s in L['steps']))
j = next(k for k, s in enumerate(Lm[i]['steps']) if s[0] not in ('L', 'sq'))
iL = next((k for k, L in enumerate(Lm) if any(s[0] == 'L' for s in L['steps'])), None)
def m_drop(c): del c['lemmas'][i]['steps'][j]
def m_prod(c): s = c['lemmas'][i]['steps'][j]; s[0] = s[1]          # claim z = u (a wrong product)
def m_end(c): c['lemmas'][i]['end'] = [c['lemmas'][i]['S'][0]] * 2 if c['lemmas'][i]['S'] else [0, 0]
def m_last(c): del c['lemmas'][-1]                                     # stop before the empty lemma
def m_word(c): c['els'][0] = c['els'][0][:2]                          # an element outside Gamma^+
def m_fwd(c):                                                         # a lemma step citing itself
    L = c['lemmas'][iL]; k = next(k for k, s in enumerate(L['steps']) if s[0] == 'L'); L['steps'][k][1] = iL
for f in (m_drop, m_prod, m_end, m_last, m_word, m_fwd):
    c = copy.deepcopy(cert); f(c)
    try: check(c); print(f.__name__, 'ACCEPTED (bad)')
    except (AssertionError, IndexError, KeyError) as e: print(f.__name__, 'rejected:', str(e) or type(e).__name__)
