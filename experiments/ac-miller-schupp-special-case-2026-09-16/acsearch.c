// Greedy best-first Andrews-Curtis search on two-generator balanced presentations.
// State: unordered pair of cyclic words up to inversion, modulo the 8 signed
// permutations of {x,y} (automorphisms of F_2; they preserve AC-triviality).
// Move: r_i <- cyclic reduction of (rotation of r_i) * (rotation of r_j)^{+-1}.
// Each move is a composite of (AC1)-(AC3). Target: some relator of length 1.
// Output: the chain of canonical states (verified independently by verify.py).
// Usage: acsearch "rel1" "rel2" maxrel maxtotal maxstates
// Letters: x X y Y (X = x^{-1}).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXL 32
typedef struct { uint64_t w[2]; uint8_t l[2]; uint32_t parent; } State;
static State *st; static uint32_t nst = 0, capst;
static uint32_t *ht; static uint64_t htcap;
static int MAXREL, MAXTOT;
static int inv(int a){ return a^1; } // 0=x 1=X 2=y 3=Y
static int sym[8][4];
static void initsym(void){
  int k=0; for(int sw=0;sw<2;sw++) for(int sx=0;sx<2;sx++) for(int sy=0;sy<2;sy++){
    int ix = sw?2:0, iy = sw?0:2;
    sym[k][0]=ix|sx; sym[k][1]=ix|(1-sx); sym[k][2]=iy|sy; sym[k][3]=iy|(1-sy); k++; }
}
// cyclically reduce in place, return new length
static int cycred(int *w, int n){
  int s[4*MAXL+8]; int m=0;
  for(int i=0;i<n;i++){ if(m>0 && s[m-1]==inv(w[i])) m--; else s[m++]=w[i]; }
  int a=0,b=m-1; while(a<b && s[a]==inv(s[b])){a++;b--;}
  int L = (m==0)?0:(b-a+1); for(int i=0;i<L;i++) w[i]=s[a+i]; return L;
}
static uint64_t pack(const int *w,int n,int start,int dir){ // dir=+1 rotation, -1 inverse
  uint64_t v=0; for(int i=0;i<n;i++){ int c; if(dir>0) c=w[(start+i)%n]; else c=inv(w[((start-i)%n+n)%n]); v=(v<<2)|c; } return v; }
static uint64_t canonword(const int *w,int n){
  uint64_t best=~0ULL; for(int s=0;s<n;s++){ uint64_t a=pack(w,n,s,1), b=pack(w,n,s,-1); if(a<best)best=a; if(b<best)best=b; } return best; }
static void unpack(uint64_t v,int n,int *w){ for(int i=n-1;i>=0;i--){ w[i]=v&3; v>>=2; } }
static void canon(int *w0,int n0,int *w1,int n1, uint64_t *o0,uint8_t *m0,uint64_t *o1,uint8_t *m1){
  uint64_t bw0=~0ULL,bw1=~0ULL; int bl0=99,bl1=99;
  int t0[MAXL],t1[MAXL];
  for(int k=0;k<8;k++){
    for(int i=0;i<n0;i++) t0[i]=sym[k][w0[i]]; for(int i=0;i<n1;i++) t1[i]=sym[k][w1[i]];
    uint64_t c0=canonword(t0,n0), c1=canonword(t1,n1); int l0=n0,l1=n1;
    if(l1<l0 || (l1==l0 && c1<c0)){ uint64_t tc=c0;c0=c1;c1=tc; int tl=l0;l0=l1;l1=tl; }
    if(l0<bl0 || (l0==bl0 && (c0<bw0 || (c0==bw0 && (l1<bl1 || (l1==bl1 && c1<bw1)))))){ bl0=l0;bw0=c0;bl1=l1;bw1=c1; }
  }
  *o0=bw0;*m0=bl0;*o1=bw1;*m1=bl1;
}
static uint64_t hsh(uint64_t a,uint64_t b,uint8_t la,uint8_t lb){ uint64_t h=a*0x9E3779B97F4A7C15ULL ^ (b+0x632BE59BD9B4E019ULL)*0xC2B2AE3D27D4EB4FULL ^ ((uint64_t)la<<8|lb)*0x165667B19E3779F9ULL; h^=h>>31; return h; }
static long find_or_add(uint64_t a,uint8_t la,uint64_t b,uint8_t lb,uint32_t parent,int *added){
  uint64_t h=hsh(a,b,la,lb)&(htcap-1);
  while(ht[h]){ State *s=&st[ht[h]-1]; if(s->w[0]==a&&s->w[1]==b&&s->l[0]==la&&s->l[1]==lb){*added=0; return ht[h]-1;} h=(h+1)&(htcap-1); }
  if(nst>=capst){ *added=-1; return -1; }
  st[nst].w[0]=a; st[nst].w[1]=b; st[nst].l[0]=la; st[nst].l[1]=lb; st[nst].parent=parent; ht[h]=nst+1; nst++; *added=1; return nst-1;
}
static int parseword(const char *s,int *w){ int n=0; for(;*s;s++){ int c; if(*s=='x')c=0; else if(*s=='X')c=1; else if(*s=='y')c=2; else if(*s=='Y')c=3; else continue; w[n++]=c; } return cycred(w,n); }
static void printword(uint64_t v,int n){ int w[MAXL]; unpack(v,n,w); const char *L="xXyY"; for(int i=0;i<n;i++) putchar(L[w[i]]); if(n==0) putchar('1'); }
// bucket queue
static uint32_t *bq[2*MAXL+2]; static uint32_t bqn[2*MAXL+2], bqc[2*MAXL+2];
static void push(int pr,uint32_t id){ if(bqn[pr]==bqc[pr]){ bqc[pr]=bqc[pr]?2*bqc[pr]:1024; bq[pr]=realloc(bq[pr],bqc[pr]*sizeof(uint32_t)); } bq[pr][bqn[pr]++]=id; }
int main(int argc,char**argv){
  if(argc<6){fprintf(stderr,"usage\n");return 1;}
  initsym(); int w0[4*MAXL],w1[4*MAXL];
  int n0=parseword(argv[1],w0), n1=parseword(argv[2],w1);
  MAXREL=atoi(argv[3]); MAXTOT=atoi(argv[4]); capst=(uint32_t)atol(argv[5]);
  if(MAXREL>MAXL) MAXREL=MAXL;
  st=malloc(sizeof(State)*capst); htcap=1; while(htcap<2ULL*capst) htcap<<=1; ht=calloc(htcap,sizeof(uint32_t));
  uint64_t a,b; uint8_t la,lb; int added; canon(w0,n0,w1,n1,&a,&la,&b,&lb);
  long id0=find_or_add(a,la,b,lb,0xFFFFFFFFu,&added); push(la+lb,(uint32_t)id0);
  long goal=-1; uint64_t expanded=0;
  while(goal<0){
    int pr=-1; for(int p=0;p<=2*MAXL;p++) if(bqn[p]){pr=p;break;} if(pr<0) break;
    uint32_t id=bq[pr][--bqn[pr]]; // LIFO within bucket
    State cur=st[id]; expanded++;
    int R[2][MAXL]; int Ln[2]={cur.l[0],cur.l[1]}; unpack(cur.w[0],Ln[0],R[0]); unpack(cur.w[1],Ln[1],R[1]);
    for(int i=0;i<2 && goal<0;i++){ int j=1-i;
      for(int ra=0;ra<Ln[i] && goal<0;ra++) for(int rb=0;rb<Ln[j] && goal<0;rb++) for(int sg=0;sg<2;sg++){
        int t[2*MAXL+2]; int n=0; for(int k=0;k<Ln[i];k++) t[n++]=R[i][(ra+k)%Ln[i]];
        if(sg==0) for(int k=0;k<Ln[j];k++) t[n++]=R[j][(rb+k)%Ln[j]];
        else for(int k=0;k<Ln[j];k++) t[n++]=inv(R[j][((rb-k)%Ln[j]+Ln[j])%Ln[j]]);
        n=cycred(t,n); if(n>MAXREL || n+Ln[j]>MAXTOT) continue;
        int o[MAXL]; for(int k=0;k<Ln[j];k++) o[k]=R[j][k];
        uint64_t ca,cb; uint8_t cla,clb; canon(t,n,o,Ln[j],&ca,&cla,&cb,&clb);
        long nid=find_or_add(ca,cla,cb,clb,id,&added);
        if(added<0){ fprintf(stderr,"state cap reached\n"); goto done; }
        if(added==1){ if(cla<=1){ goal=nid; break; } push(cla+clb,(uint32_t)nid); }
      }
    }
  }
done:
  printf("states %u expanded %llu\n",nst,(unsigned long long)expanded);
  if(goal>=0){ printf("FOUND\n"); long c=goal; int depth=0; long chain[100000]; while(c!=0xFFFFFFFFL && c>=0){ chain[depth++]=c; if(st[c].parent==0xFFFFFFFFu) break; c=st[c].parent; }
    for(int k=depth-1;k>=0;k--){ State *s=&st[chain[k]]; printword(s->w[0],s->l[0]); putchar(' '); printword(s->w[1],s->l[1]); putchar('\n'); }
  } else printf("NOTFOUND\n");
  return 0;
}
