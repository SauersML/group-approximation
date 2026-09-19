"""Rewrite w(a,t) in the basis x = a, y = t a^m (t = y x^-m) or y = a^m t (t = x^-m y).
Prints the cyclically reduced relator w'(x,y) with x -> 'a', y -> 't'.  Usage: rebase.py file m side"""
import sys
m, side = int(sys.argv[2]), sys.argv[3]
def red(w):
    o=[]
    for c in w:
        if o and o[-1]==c.swapcase(): o.pop()
        else: o.append(c)
    while len(o)>1 and o[0]==o[-1].swapcase(): o=o[1:-1]
    return ''.join(o)
xm = ('A'*m if m>0 else 'a'*(-m))
Xm = ('a'*m if m>0 else 'A'*(-m))
sub = {'a':'a','A':'A'}
if side=='R': sub['t']='t'+xm; sub['T']=Xm+'T'
else: sub['t']=xm+'t'; sub['T']='T'+Xm
for line in open(sys.argv[1]):
    f=line.split()
    if not f: continue
    print(red(''.join(sub[c] for c in f[0])), f[0])
