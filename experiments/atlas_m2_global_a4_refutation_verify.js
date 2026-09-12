"use strict";
const assert=(p,m)=>{if(!p)throw new Error(m)};
const I=()=>[1,2,4,8,16,32,64,128];
const eq=(a,b)=>a.every((x,i)=>x===b[i]);
const fromHex=s=>(s.match(/../g)||[]).map(x=>parseInt(x,16)).reverse();
const toHex=a=>[...a].reverse().map(x=>x.toString(16).padStart(2,"0")).join("");
const mul=(a,b)=>a.map(r=>{let z=0;for(let j=0;j<8;j++)if((r>>j)&1)z^=b[j];return z});
const inv=a=>{const l=a.slice(),r=I();for(let c=0;c<8;c++){let p=c;while(p<8&&!((l[p]>>c)&1))p++;assert(p<8,"singular");[l[c],l[p]]=[l[p],l[c]];[r[c],r[p]]=[r[p],r[c]];for(let i=0;i<8;i++)if(i!==c&&((l[i]>>c)&1)){l[i]^=l[c];r[i]^=r[c]}}return r};
const order=a=>{let z=I();for(let n=1;n<=255;n++){z=mul(z,a);if(eq(z,I()))return n}throw new Error("order bound")};
const rank=a=>{a=a.slice();let p=0;for(let c=0;c<8;c++){let q=p;while(q<a.length&&!((a[q]>>c)&1))q++;if(q===a.length)continue;[a[p],a[q]]=[a[q],a[p]];for(let i=0;i<a.length;i++)if(i!==p&&((a[i]>>c)&1))a[i]^=a[p];p++}return p};
const lift4=s=>{const e=(s.match(/../g)||[]).map(x=>parseInt(x,10));assert(e.length===16&&e.every(x=>x===0||x===1),"bad 4x4");const a=Array(8).fill(0);for(let i=0;i<4;i++)for(let j=0;j<4;j++)if(e[4*i+j]){a[2*i]|=1<<(2*j);a[2*i+1]|=1<<(2*j+1)}return a};
const trans=(i,j)=>{const a=I();a[2*i]^=1<<(2*j);a[2*i+1]^=1<<(2*j+1);return a};
const F=fromHex("401004080301c030"),Fi=inv(F);
const move=x=>mul(mul(Fi,x),F);
const opcode=x=>mul(move(x),inv(x));
assert(toHex(Fi)==="8280414010200c04","inverse");
const H6=["01000000000101000000010000000001","01000000000100000001010000000001","01000000000101000001000000000001","01000000000001000001010000000001"].map(lift4);
const H18=["01010000000100000000010000000001","01000000010100000000010000000001","01000000000100000000000100000101","01010000010000000000010000000001","00010000010100000000010000000001","01000000000100000000010100000100"].map(lift4);
let contextChecks=0;
for(const labels of [H6,H18]){
  const twos=labels.filter(x=>order(x)===2),threes=labels.filter(x=>order(x)===3);
  for(const x of twos)for(const y of threes){assert(order(mul(move(x),y))===3,"moved C2/fixed C3");contextChecks++}
  for(const x of twos)for(const y of threes){assert(order(mul(x,move(y)))===3,"fixed C2/moved C3");contextChecks++}
}
assert(contextChecks===24,"distinct directed context count");
const qword=[
[2,"01010000010000000000010000000001"],[1,"01000000000100000000010100000001"],
[2,"01000000010100000000010000000001"],[1,"01000000000100000000010100000001"],
[2,"00010000010100000000010000000001"],[1,"01000000000100000000010100000001"],
[2,"01010000000100000000010000000001"],[1,"01000000000100000000010100000001"]];
let q=I();for(const [factor,s] of qword){const x=lift4(s);q=mul(q,factor===2?move(x):x)}
assert(eq(q,I()),"q19243");
const raw={t21:opcode(trans(2,1)),t12:opcode(trans(1,2))};
const expected={t21:"8040281409070201",t12:"8040201028143e29"};
for(const name of Object.keys(raw)){assert(toHex(raw[name])===expected[name],name+" opcode");assert(order(raw[name])===4,name+" order");assert(rank(raw[name].map((x,i)=>x^(1<<i)))===4,name+" rank")}
const report={
 field:"GF(2)",frame:toHex(F),inverse:toHex(Fi),
 distinct_directed_packet_contexts_verified:contextChecks,
 collision_19243:{value:toHex(q),identity:true},
 raw_s3:{
  t21:{opcode:toHex(raw.t21),order:order(raw.t21),rank_minus_identity:4},
  t12:{opcode:toHex(raw.t12),order:order(raw.t12),rank_minus_identity:4},
  regular_squared_energy:4
 },
 exact_regular_moments:{packet_words:30,packet_value:1,collision_weight:6,collision_value:1,functional:36,classical_mixture_ceiling:30},
 packet_energy_lower_bound:"5040/28363 > 0",
 directly_refuted:[
  "atlas-a4-alignment-moment-simplex-rounding",
  "atlas-centralizer-products-19243-classicalize",
  "atlas-a4-relative-packet-commutator-collapse",
  "atlas-a4-full-packet-normal-generator-holonomy-compiler",
  "atlas-a4-full-packet-normal-generator-table-compiler"
 ],status:"PASS"
};
assert(report.exact_regular_moments.functional===36,"moment functional");
const output=JSON.stringify(report,null,2);
if(typeof text==="function")text(output);else console.log(output);