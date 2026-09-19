# cone.py in.jsonl k R SHORT : cone-lemma certificate for record k of in.jsonl.
#  1. ctree dumps the positive-cone CNF of the radius-R ball (short-SHORT products) and its variable map;
#  2. the CNF is re-derived clause by clause from the rewriting normal form of lo_census.VH (semcheck):
#     every variable is a kernel element, "x or x^-1" and "not both" for each inverse pair, and every
#     clause (-a -b c) / (-a -b) has a*b = c / a*b = 1 in the group;
#  3. Glucose 4 (pysat) produces a DRAT proof of unsatisfiability, used only as a *source of lemmas*;
#  4. rup (own C++ unit propagation) checks every lemma is a RUP consequence, trims to a core, and the
#     core is checked again from scratch. A RUP-checked empty clause over sound axioms proves Gamma^+ not LO.
import sys, json, os, subprocess, time
from sample import VH, ctree, parse
from vh_enum import inv_arr
here = os.path.dirname(os.path.abspath(__file__)); TMP = os.environ.get('TMPD', '/tmp')

def semcheck(G, cnf):
    mp = {}
    for l in open(cnf + '.map'):
        v, w, iv = l.split(); mp[int(v)] = (parse(G, w), int(iv))
    def ev(g):
        a = sum(1 for c in g if c[0] == 'v'); return len(g) > 0 and a % 2 == 0 and (len(g) - a) % 2 == 0
    def inv(g): return G.rw([(c[0], (G.iA if c[0] == 'h' else G.iB)[c[1]]) for c in reversed(g)])
    for v, (g, iv) in mp.items():
        if not ev(g) or mp[iv][0] != inv(g): return 'bad variable %d' % v
    nbad = 0; n = 0
    for l in open(cnf):
        if l[0] == 'p': continue
        c = list(map(int, l.split()))[:-1]; n += 1
        if len(c) == 2 and c[0] > 0 and c[1] > 0: ok = mp[c[0]][1] == c[1]            # x or x^-1
        elif len(c) == 2 and c[0] < 0 and c[1] < 0:                                   # not both / a b = 1
            a, b = mp[-c[0]][0], mp[-c[1]][0]; ok = mp[-c[0]][1] == -c[1] or G.rw(list(a) + list(b)) == ()
        elif len(c) == 3 and c[0] < 0 and c[1] < 0 and c[2] > 0:
            ok = G.rw(list(mp[-c[0]][0]) + list(mp[-c[1]][0])) == mp[c[2]][0]
        else: ok = False
        nbad += not ok
    return 'ok %d clauses' % n if nbad == 0 else 'BAD %d clauses' % nbad

def run(r, R, sh):
    m, pA, n, pB = int(r['pat'][0]), int(r['pat'][1]), int(r['pat'][3]), int(r['pat'][4])
    G = VH(inv_arr(m, pA), inv_arr(n, pB), {tuple(a): tuple(b) for a, b in r['sq']}); G.confluence()
    f = os.path.join(TMP, 'w13c_%d.cnf' % os.getpid()); t0 = time.time()
    ctree(G, R, sh, 0, 0, cnf=f); out = dict(pat=r['pat'], seed=r['seed'], k=r['k'], R=R, short=sh)
    out['sem'] = semcheck(G, f); t1 = time.time()
    from pysat.formula import CNF
    from pysat.solvers import Solver
    F = CNF(from_file=f); out['nv'], out['nc'] = F.nv, len(F.clauses)
    with Solver(name='glucose4', bootstrap_with=F.clauses, with_proof=True) as s:
        res = s.solve(); out['sat'] = res
        if not res:
            with open(f + '.drat', 'w') as g:
                for line in s.get_proof(): g.write(line + '\n')
    del F; t2 = time.time()
    if not res:
        p = subprocess.run([os.path.join(here, 'rup'), f, f + '.drat'], capture_output=True, text=True)
        out['rup'] = p.stdout.strip()
        q = subprocess.run([os.path.join(here, 'rup'), f, f + '.drat.core'], capture_output=True, text=True)
        out['rup_core'] = q.stdout.strip()
        out['cert'] = out['sem'].startswith('ok') and out['rup'].startswith('RUP-OK') and q.stdout.startswith('RUP-OK')
        wd = {int(l.split()[0]): l.split()[1] for l in open(f + '.map')}   # save the core as words
        os.makedirs(os.path.join(here, 'certs'), exist_ok=True)
        core = [[('+' if x > 0 else '-') + wd[abs(x)] for x in map(int, l.split()[:-1])] for l in open(f + '.drat.core')]
        json.dump(dict(pat=r['pat'], seed=r['seed'], k=r['k'], R=R, short=sh, lemmas=core),
                  open(os.path.join(here, 'certs', '%s_s%d_k%d_R%ds%d.json' % (r['pat'], r['seed'], r['k'], R, sh)), 'w'))
    out['sec'] = [round(t1 - t0), round(t2 - t1), round(time.time() - t2)]
    for e in ('', '.map', '.drat', '.drat.core', '.drat.core.core', '.drat.inputs', '.drat.core.inputs'):
        if os.path.exists(f + e): os.unlink(f + e)
    return out

if __name__ == '__main__':
    recs = [json.loads(l) for l in open(sys.argv[1])]
    R, sh = int(sys.argv[3]), int(sys.argv[4])
    for k in sys.argv[2].split(','):
        print(json.dumps(run(recs[int(k)], R, sh))); sys.stdout.flush()
