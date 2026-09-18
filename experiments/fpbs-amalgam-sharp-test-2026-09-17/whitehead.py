inv=lambda w: ''.join(ch.swapcase() for ch in reversed(w))
def red(w):
    s=[]
    for ch in w:
        if s and s[-1]==ch.swapcase(): s.pop()
        else: s.append(ch)
    return ''.join(s)
def cyc(w):
    w=red(w)
    while len(w)>1 and w[0]==w[-1].swapcase(): w=w[1:-1]
    return w
def app(phi,w): return red(''.join(phi[ch] if ch.islower() else inv(phi[ch.lower()]) for ch in w))
v='cdcDcd'
best=len(cyc(v))
for y in 'cCdD':
    x='d' if y.lower()=='c' else 'c'
    for img in [x+y, inv(y)+x, inv(y)+x+y]:
        phi={y.lower():y.lower(), x:img}
        w=cyc(app(phi,v)); print(y,img,w,len(w))
print('---greedy')
def whs():
    for y in 'cCdD':
        x='d' if y.lower()=='c' else 'c'
        for img in [x+y, inv(y)+x, inv(y)+x+y]:
            yield {y.lower():y.lower(), x:img}
for start in ['cdcDcd','abaBab'.replace('a','c').replace('b','d').replace('B','D')]:
    w=cyc(start); print(start)
    while True:
        cand=min((cyc(app(p,w)) for p in whs()), key=len)
        if len(cand)<len(w): w=cand; print('  ',w)
        else: break
