var soe  {time} := soe0;
var qch  {time};
var qdis {time};
var qbat {time};
var qqbat {time};
#var xch {time} binary;

var cos_norm {t in time, (n,m) in buspair: Ccond[t,n,m]} = sqrt( (cv1[t,n,m]-lambda14[t,n,m])^2 + (cv2[t,n,m]-lambda15[t,n,m])^2 );
var cos_l1 {t in time, (n,m) in buspair: Ccond[t,n,m]} = sqrt( (cv3[t,n,m]-lambda16[t,n,m] - cos_norm[t,n,m])^2 + 4*eps^2 );
var cos_l2 {t in time, (n,m) in buspair: Ccond[t,n,m]} = sqrt( (cv3[t,n,m]-lambda16[t,n,m] + cos_norm[t,n,m])^2 + 4*eps^2 );

var vsoa_norm {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} = sqrt( (v1[t,l,n,m]-lambda17[t,l,n,m])^2 + (v2[t,l,n,m]-lambda18[t,l,n,m])^2 + (v3[t,l,n,m]-lambda19[t,l,n,m])^2 );
var vsoa_l1 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} = sqrt( (v4[t,l,n,m]-lambda20[t,l,n,m] - vsoa_norm[t,l,n,m])^2 + 4*eps^2 );
var vsoa_l2 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]} = sqrt( (v4[t,l,n,m]-lambda20[t,l,n,m] + vsoa_norm[t,l,n,m])^2 + 4*eps^2 );

var pq_norm {t in time, (l,n,m) in branch: Scond[t,l,n,m]} = sqrt( (P[t,l,n,m]-lambda11[t,l,n,m])^2 + (Q[t,l,n,m]-lambda12[t,l,n,m])^2 );
var pq_l1 {t in time, (l,n,m) in branch: Scond[t,l,n,m]} = sqrt( (Sl_max[l]-lambda13[t,l,n,m] - pq_norm[t,l,n,m])^2 + 4*eps^2 );
var pq_l2 {t in time, (l,n,m) in branch: Scond[t,l,n,m]} = sqrt( (Sl_max[l]-lambda13[t,l,n,m] + pq_norm[t,l,n,m])^2 + 4*eps^2 );


subject to soe_c1 {t in time}:
 soe[t] = (if ord(t)>1 then soe[prev(t)] else soe0 ) + qch[t]*eta_ch - qdis[t]/eta_dis;
 
subject to q_sum {t in time}:
 qbat[t] = qch[t] - qdis[t];
 
subject to soe_c2 {t in time}:
 0 <= soe[t] <= soe_max;


subject to soe_c3 {t in time}:
 0 <= qch [t] <= ch_max;

subject to soe_c4 {t in time}:
 0 <= qdis[t] <= dis_max;
 
subject to soe_c5 {t in time}:
 qbat[t]^2 + qqbat[t]^2 <= ch_max^2;

/*
subject to soe_c3_1 {t in time}:
 0 <= qch [t];

subject to soe_c3_2 {t in time}:
	  qch [t] <= ch_max*xch[t];

subject to soe_c4_1 {t in time}:
 0 <= qdis [t];

subject to soe_c4_2 {t in time}:
	  qdis [t] <= dis_max*(1-xch[t]);
*/
 
subject to bus_p_soa_m {t in time, n in bus}:
 sum {(n,g) in bus_gen} Pgen[t,g] - sum {(n,lo) in bus_load} pd[lo]*load_f[t] -(if n in es_bus then qbat[t])
-sum {(l,n,m) in branch} P[t,l,n,m] - sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*gs[sh] = 0;

subject to bus_q_soa_m {t in time, n in bus}:
 sum {(n,g) in bus_gen} Qgen[t,g] - sum {(n,lo) in bus_load} qd[lo]*load_f[t] -(if n in es_bus then qqbat[t])
-sum {(l,n,m) in branch} Q[t,l,n,m] + sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*bs[sh] = 0;

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

subject to Pgencc {t in time, g in gen: c2[g]>0}:
 c1[g] + mi1max[t,g] - mi1min[t,g] + sum {(n,g) in bus_gen} lambda1[t,n] + 2*c2[g]*Pgen[t,g] = 0;
 
subject to pgmaxcc {t in time, g in gen}:
( pg_max[g] - Pgen[t,g] + mi1max[t,g] )/2 - sqrt( ( pg_max[g] - Pgen[t,g] - mi1max[t,g] )^2 + 4*eps^2 )/2 = 0;

subject to pgmincc {t in time, g in gen}:
(-pg_min[g] + Pgen[t,g] + mi1min[t,g] )/2 - sqrt( (-pg_min[g] + Pgen[t,g] - mi1min[t,g] )^2 + 4*eps^2 )/2 = 0;

subject to qgmaxcc {t in time, g in gen}:
( qg_max[g] - Qgen[t,g] + mi2max[t,g] )/2 - sqrt( ( qg_max[g] - Qgen[t,g] - mi2max[t,g] )^2 + 4*eps^2 )/2 = 0;

subject to qgmincc {t in time, g in gen}:
(-qg_min[g] + Qgen[t,g] + mi2min[t,g] )/2 - sqrt( (-qg_min[g] + Qgen[t,g] - mi2min[t,g] )^2 + 4*eps^2 )/2 = 0;

subject to vmaxcc {t in time, n in bus}:
( vmax[n] - dV[t,n] - Vt[t,n] + mi3max[t,n] )/2 - sqrt( ( vmax[n] - dV[t,n] - Vt[t,n] - mi3max[t,n] )^2 + 4*eps^2 )/2 = 0;

subject to vmincc {t in time, n in bus}:
(-vmin[n] + dV[t,n] + Vt[t,n] + mi3min[t,n] )/2 - sqrt( (-vmin[n] + dV[t,n] + Vt[t,n] - mi3min[t,n] )^2 + 4*eps^2 )/2 = 0;



subject to cosa_cc3 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
(cv3[t,n,m]+lambda16[t,n,m])/2 - (cos_l1[t,n,m] + cos_l2[t,n,m])/4 = 0;

subject to cosa_cc1 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
(cv1[t,n,m]+lambda14[t,n,m])/2 - (cv1[t,n,m]-lambda14[t,n,m])*(-cos_l1[t,n,m] + cos_l2[t,n,m])/cos_norm[t,n,m]/4 = 0;

subject to cosa_cc2 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
(cv2[t,n,m]+lambda15[t,n,m])/2 - (cv2[t,n,m]-lambda15[t,n,m])*(-cos_l1[t,n,m] + cos_l2[t,n,m])/cos_norm[t,n,m]/4 = 0;


subject to vsoa_cc4 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
(v4[t,l,n,m]+lambda20[t,l,n,m])/2 - (vsoa_l1[t,l,n,m] + vsoa_l2[t,l,n,m])/4 = 0;

subject to vsoa_cc1 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
(v1[t,l,n,m]+lambda17[t,l,n,m])/2 - (v1[t,l,n,m]-lambda17[t,l,n,m])*(-vsoa_l1[t,l,n,m] + vsoa_l2[t,l,n,m])/vsoa_norm[t,l,n,m]/4 = 0;

subject to vsoa_cc2 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
(v2[t,l,n,m]+lambda18[t,l,n,m])/2 - (v2[t,l,n,m]-lambda18[t,l,n,m])*(-vsoa_l1[t,l,n,m] + vsoa_l2[t,l,n,m])/vsoa_norm[t,l,n,m]/4 = 0;

subject to vsoa_cc3 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
(v3[t,l,n,m]+lambda19[t,l,n,m])/2 - (v3[t,l,n,m]-lambda19[t,l,n,m])*(-vsoa_l1[t,l,n,m] + vsoa_l2[t,l,n,m])/vsoa_norm[t,l,n,m]/4 = 0;


subject to pqmax_cc3 {t in time, (l,n,m) in branch: Scond[t,l,n,m]}:
(Sl_max[l]+lambda13[t,l,n,m])/2 - (pq_l1[t,l,n,m] + pq_l2[t,l,n,m])/4 = 0;

subject to pqmax_cc1 {t in time, (l,n,m) in branch: Scond[t,l,n,m]}:
(P[t,l,n,m]+lambda11[t,l,n,m])/2 - (P[t,l,n,m]-lambda11[t,l,n,m])*(-pq_l1[t,l,n,m] + pq_l2[t,l,n,m])/pq_norm[t,l,n,m]/4 = 0;

subject to pqmax_cc2 {t in time, (l,n,m) in branch: Scond[t,l,n,m]}:
(Q[t,l,n,m]+lambda12[t,l,n,m])/2 - (Q[t,l,n,m]-lambda12[t,l,n,m])*(-pq_l1[t,l,n,m] + pq_l2[t,l,n,m])/pq_norm[t,l,n,m]/4 = 0;














 