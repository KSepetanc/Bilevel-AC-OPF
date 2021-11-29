var soe  {time} := soe0;
var qch  {time};
var qdis {time};
var qbat {time};
var wb {time,be_set};
var wch {time};
var wdis {time};
var xb {time, be_set} binary;
var yb {time} integer;
var xch {time} binary;

var qqch  {time};
var qqdis {time};
var qqbat {time};
var wqb {time,be_set};
var wqch {time};
var wqdis {time};
var xqb {time, be_set} binary;
var yqb {time} integer;
var xqch {time} binary;

subject to yblimits {t in time}:
 0 <= yb[t] <= be_max;

subject to soe_c1 {t in time}:
 soe[t] = (if ord(t)>1 then soe[prev(t)] else soe0 ) + qch[t]*eta_ch - qdis[t]/eta_dis;
 
subject to q_sum {t in time}:
 qbat[t] = qch[t] - qdis[t];
 
subject to soe_c2 {t in time}:
 0 <= soe[t] <= soe_max;

subject to soe_c3_1 {t in time}:
 0 <= qch [t];
 
subject to soe_c3_2 {t in time}:
 qch [t] <= ch_max*xch[t];

subject to soe_c4_1 {t in time}:
 0 <= qdis[t];

subject to soe_c4_2 {t in time}:
 qdis[t] <= dis_max*(1-xch[t]);
 
subject to soe_c5 {t in time}:
 qbat[t]^2 + qqbat[t]^2 <= ch_max^2;
 
subject to bus_p_soa_m {t in time, n in bus}:
 sum {(n,g) in bus_gen} Pgen[t,g] - sum {(n,lo) in bus_load} pd[lo]*load_f[t] -(if n in es_bus then qbat[t])
-sum {(l,n,m) in branch} P[t,l,n,m] - sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*gs[sh] = 0;

subject to bus_q_soa_m {t in time, n in bus}:
 sum {(n,g) in bus_gen} Qgen[t,g] - sum {(n,lo) in bus_load} qd[lo]*load_f[t] -(if n in es_bus then qqbat[t])
-sum {(l,n,m) in branch} Q[t,l,n,m] + sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*bs[sh] = 0;


subject to strong_duality:
 sum {t in time, g in gen} (c2[g]*Pgen[t,g]^2 + c1[g]*Pgen[t,g] + c0[g]) <= 0*eps +
-sum {t in time}							             (wch[t]-wdis[t]+wqch[t]-wqdis[t])
-sum {t in time, g in gen: c2[g]>0}                      (c1[g]+mi1max[t,g]-mi1min[t,g]+sum{(n,g) in bus_gen} lambda1[t,n])^2/(4*c2[g])
+sum {t in time, n in refbus}                            fit[t,n]*lambda7[t,n]
+sum {t in time, g in gen}                               (c0[g]-pg_max[g]*mi1max[t,g]+pg_min[g]*mi1min[t,g]-qg_max[g]*mi2max[t,g]+qg_min[g]*mi2min[t,g])
-sum {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} (lambda17[t,l,n,m]+lambda20[t,l,n,m])/2  
+sum {t in time, n in bus}                               ((Vt[t,n]-vmax[n])*mi3max[t,n] + (vmin[n]-Vt[t,n])*mi3min[t,n])
-sum {t in time, (n,lo) in bus_load}                     (pd[lo]*load_f[t]*lambda1[t,n]+qd[lo]*load_f[t]*lambda2[t,n]) 
-sum {t in time, (n,sh) in bus_shunt}                    (gs[sh]*Vt[t,n]^2*lambda1[t,n]-bs[sh]*Vt[t,n]^2*lambda2[t,n])
+sum {t in time, (n,m) in buspair: Ccond[t,n,m]}         ((3/4)*lambda15[t,n,m] - (5/4)*lambda16[t,n,m]) 
-sum {t in time, (n,m) in buspair:!Ccond[t,n,m]}         lambda22[t,n,m]
-sum {t in time, (l,n,m) in branch_from}                 ((gl[l]+gl_fr[l])*lambda3[t,l,n,m]-(bl[l]+bl_fr[l])*lambda5[t,l,n,m])*Vt[t,n]^2/tap[l]^2
-sum {t in time, (l,n,m) in branch_to}                   ((gl[l]+gl_to[l])*lambda4[t,l,n,m]-(bl[l]+bl_to[l])*lambda6[t,l,n,m])*Vt[t,n]^2
-sum {t in time, (l,n,m) in branch: Scond[t,l,n,m]}      Sl_max[l]*lambda13[t,l,n,m];

maximize UpQPOF: 
-sum {t in time, g in gen} (c2[g]*Pgen[t,g]^2 + c1[g]*Pgen[t,g] + c0[g])

-sum {t in time, g in gen: c2[g]>0}                      (c1[g]+mi1max[t,g]-mi1min[t,g]+sum{(n,g) in bus_gen} lambda1[t,n])^2/(4*c2[g])
+sum {t in time, n in refbus}                            fit[t,n]*lambda7[t,n]
+sum {t in time, g in gen}                               (c0[g]-pg_max[g]*mi1max[t,g]+pg_min[g]*mi1min[t,g]-qg_max[g]*mi2max[t,g]+qg_min[g]*mi2min[t,g])
-sum {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} (lambda17[t,l,n,m]+lambda20[t,l,n,m])/2  
+sum {t in time, n in bus}                               ((Vt[t,n]-vmax[n])*mi3max[t,n] + (vmin[n]-Vt[t,n])*mi3min[t,n])
-sum {t in time, (n,lo) in bus_load}                     (pd[lo]*load_f[t]*lambda1[t,n]+qd[lo]*load_f[t]*lambda2[t,n]) 
-sum {t in time, (n,sh) in bus_shunt}                    (gs[sh]*Vt[t,n]^2*lambda1[t,n]-bs[sh]*Vt[t,n]^2*lambda2[t,n])
+sum {t in time, (n,m) in buspair: Ccond[t,n,m]}         ((3/4)*lambda15[t,n,m] - (5/4)*lambda16[t,n,m]) 
-sum {t in time, (n,m) in buspair:!Ccond[t,n,m]}         lambda22[t,n,m]
-sum {t in time, (l,n,m) in branch_from}                 ((gl[l]+gl_fr[l])*lambda3[t,l,n,m]-(bl[l]+bl_fr[l])*lambda5[t,l,n,m])*Vt[t,n]^2/tap[l]^2
-sum {t in time, (l,n,m) in branch_to}                   ((gl[l]+gl_to[l])*lambda4[t,l,n,m]-(bl[l]+bl_to[l])*lambda6[t,l,n,m])*Vt[t,n]^2
-sum {t in time, (l,n,m) in branch: Scond[t,l,n,m]}      Sl_max[l]*lambda13[t,l,n,m];

subject to q_int {t in time}:
 qch[t]/ch_max + qdis[t]/dis_max = yb[t]/be_max;

subject to bin_exp1 {t in time}:
 yb[t] = sum {be in be_set} 2^(ord(be)-1)*xb[t,be];
 
subject to bin_exp2 {t in time}:
 wch[t]/ch_max + wdis[t]/dis_max = sum {be in be_set} 2^(ord(be)-1)*wb[t,be]/be_max;

subject to wchb1 {t in time}:
 wch[t] <= max(0,lambda1up[t])*ch_max*xch[t];
 
subject to wchb2 {t in time}:
 wch[t] >= min(0,lambda1dn[t])*ch_max*xch[t];
 
subject to wdisb1 {t in time}:
 wdis[t] <= max(0,lambda1up[t])*dis_max*(1-xch[t]);
 
subject to wdisb2 {t in time}:
 wdis[t] >= min(0,lambda1dn[t])*dis_max*(1-xch[t]);


subject to wb_under1 {t in time, be in be_set}:
 wb[t,be] >= xb[t,be]*lambda1dn[t];
 
subject to wb_under2 {t in time, es in es_bus, be in be_set}:
 wb[t,be] >= lambda1[t,es] + xb[t,be]*lambda1up[t] - lambda1up[t];
 
subject to wb_over1 {t in time, es in es_bus, be in be_set}:
 wb[t,be] <= lambda1[t,es] + xb[t,be]*lambda1dn[t] - lambda1dn[t];

subject to wb_over2 {t in time, be in be_set}:
 wb[t,be] <= xb[t,be]*lambda1up[t];



subject to qq_sum {t in time}:
 qqbat[t] = qqch[t] - qqdis[t];

subject to soe_c3_1q {t in time}:
 0 <= qqch [t];
 
subject to soe_c3_2q {t in time}:
 qqch [t] <= ch_max*xqch[t];

subject to soe_c4_1q {t in time}:
 0 <= qqdis[t];

subject to soe_c4_2q {t in time}:
 qqdis[t] <= dis_max*(1-xqch[t]);
 
 

subject to yqblimits {t in time}:
 0 <= yqb[t] <= be_max;

subject to qq_int {t in time}:
 qqch[t]/ch_max + qqdis[t]/dis_max = yqb[t]/be_max;
 
subject to qbin_exp1 {t in time}:
 yqb[t] = sum {be in be_set} 2^(ord(be)-1)*xqb[t,be];
 
subject to qbin_exp2 {t in time}:
 wqch[t]/ch_max + wqdis[t]/dis_max = sum {be in be_set} 2^(ord(be)-1)*wqb[t,be]/be_max;

subject to wchb1q {t in time}:
 wqch[t] <= max(0,lambda2up[t])*ch_max*xqch[t];
 
subject to wchb2q {t in time}:
 wqch[t] >= min(0,lambda2dn[t])*ch_max*xqch[t];
 
subject to wdisb1q {t in time}:
 wqdis[t] <= max(0,lambda2up[t])*dis_max*(1-xqch[t]);
 
subject to wdisb2q {t in time}:
 wqdis[t] >= min(0,lambda2dn[t])*dis_max*(1-xqch[t]);


subject to wqb_under1 {t in time, be in be_set}:
 wqb[t,be] >= xqb[t,be]*lambda2dn[t];
 
subject to wqb_under2 {t in time, es in es_bus, be in be_set}:
 wqb[t,be] >= lambda2[t,es] + xqb[t,be]*lambda2up[t] - lambda2up[t];
 
subject to wqb_over1 {t in time, es in es_bus, be in be_set}:
 wqb[t,be] <= lambda2[t,es] + xqb[t,be]*lambda2dn[t] - lambda2dn[t];

subject to wqb_over2 {t in time, be in be_set}:
 wqb[t,be] <= xqb[t,be]*lambda2up[t];



/*
subject to xbin0 {t in time, be in be_set}:
 xb[t,be] = (if be="be1" then 1 else 0) ;
 
#(if be="be1" then 1 else 0) 

subject to ybin0 {t in time}:
 yb[t] = 1;
 
subject to xch0 {t in time}:
 xch[t] = 0;

subject to xbin0q {t in time, be in be_set}:
 xqb[t,be] = (if be="be1" then 1 else 0);

subject to ybin0q {t in time}:
 yqb[t] = 1;
 
subject to xch0q {t in time}:
 xqch[t] = 0;
*/

				 