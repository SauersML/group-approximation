# The index-3 cover X_K of X for the explicit example: x = (1 2), y = (0 1) on vertices {0,1,2}.
# Checks that Gamma is X_K^1 minus the single x-edge f: 2 -> 1, that w lifts to closed loops at all
# three vertices, and prints the third lift (based at 2) as a letter/edge sequence.
w="xyyyyXYxyyXYYYYY"
px={0:0,1:2,2:1}; py={0:1,1:0,2:2}
inv=lambda p:{v:k for k,v in p.items()}
act={'x':px,'y':py,'X':inv(px),'Y':inv(py)}
cover=sorted([(v,px[v],'x') for v in px]+[(v,py[v],'y') for v in py])
gamma=sorted([(0,0,'x'),(1,2,'x'),(0,1,'y'),(1,0,'y'),(2,2,'y')])
print("cover edges minus Gamma:",[e for e in cover if e not in gamma])
for v0 in range(3):
    v=v0; seq=[]
    for ch in w:
        u=act[ch][v]
        e=(v,u,ch) if ch.islower() else (u,v,ch.lower())
        seq.append(('f' if e not in gamma else '')+ch); v=u
    print("lift at",v0,"closed:",v==v0,"uses f:",sum(1 for z in seq if z[0]=='f'),' '.join(seq))
