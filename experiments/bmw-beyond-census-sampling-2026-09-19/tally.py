# tally.py batch.jsonl : one line per sample with the certificate that closed it, then totals per pattern.
import sys, json, collections
def verdict(r):
    if not r['cand']: return 'reducible (finite automaton)'
    if r.get('tree4') and r['tree4'][2]: return 'R4 cone tree'
    if r.get('tree6s4') and r['tree6s4'][2]: return 'R6s4 cone tree'
    c = r.get('cone6s4') or {}
    if c.get('cert'): return 'R6s4 RUP cone lemmas'
    return 'SURVIVOR (sat=%s)' % c.get('sat')
tot = collections.defaultdict(collections.Counter)
for l in open(sys.argv[1]):
    r = json.loads(l); v = verdict(r); tot[r['pat']][v] += 1
    print(r['pat'], r['seed'], v, 'klein=%s' % r.get('klein'))
for p, c in tot.items(): print('TOTAL', p, dict(c))
