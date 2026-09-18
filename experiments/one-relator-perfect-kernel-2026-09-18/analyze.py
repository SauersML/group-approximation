import sys, ast
from whitehead import wh_min
def ws(W): return ''.join(('xyz'[x-1]) if x>0 else 'XYZ'[-x-1] for x in W)
for line in open(sys.argv[1]):
    if not line.startswith('OPEN'): continue
    seq=ast.literal_eval(line[line.index('seq')+4:line.rindex(']')+1])
    W=[]
    for h,e in seq: W += [h+1 if e>0 else -(h+1)]*abs(e)
    m=wh_min(W,max(h for h,_ in seq)+1)
    print(line.split()[1], 'W0',ws(W),'whmin',ws(m), 'FREE' if len(m)==1 else 'NONFREE')
