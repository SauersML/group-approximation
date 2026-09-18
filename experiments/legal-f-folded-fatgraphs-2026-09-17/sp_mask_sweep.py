"""Masked support propagation sweep (memory r word-free LP, power m).
For each entry and each two-letter mask {x,y} (windows = boundary-word windows of the
d^- darts restricted to letters x,y and inverses), run exact arc-consistency support
propagation (sp_mask.propagate) and report whether anything survives.  An empty
survivor set proves: no legal f^m-folded fatgraph has all d^- boundary words over {x,y}^{+-1}."""
import sys, json, time
import lp_memory as LM, lp_allwords as LA, sp_mask as SP
d=json.load(open('phi_scan4.json'))
ids=[int(x) for x in sys.argv[1].split(',')]; m=int(sys.argv[2]); r=int(sys.argv[3])
masks=sys.argv[4].split(',') if len(sys.argv)>4 else ['abAB','acAC','bcBC']
for i in ids:
    phi0=d[i][2]; phi=LA.power(phi0,m); g=LA.gates(phi)
    TY=LM.MTypes(phi,g,r)
    for mk in masks:
        t=time.time(); al=set(mk)
        mask=[set(v)<=al for v in TY.windows]
        walive,S=SP.propagate(TY,g,4,log=lambda *a,**k:None,wmask=mask)
        alive=["".join(v) for j,v in enumerate(TY.windows) if walive[j]]
        hf=SP.homology_feasible(TY,walive) if walive.any() else False
        print(i,json.dumps(phi0),"m",m,"r",r,"mask",mk,"inmask",sum(mask),"alive",len(alive),"homfeas",hf,"t %.0f"%(time.time()-t),alive[:12],flush=True)
