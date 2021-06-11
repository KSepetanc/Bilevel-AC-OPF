var soe  {time} := soe0;
var qch  {time};
var qdis {time};
var qbat {time};

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
 
subject to bus_p_soa_m {t in time, n in bus}:
 sum {(n,g) in bus_gen} Pgen[t,g] - sum {(n,lo) in bus_load} pd[lo]*load_f[t] -(if n in es_bus then qbat[t])
-sum {(l,n,m) in branch} P[t,l,n,m] - sum{(n,sh) in bus_shunt} (Vt[t,n]^2+2*Vt[t,n]*dV[t,n])*gs[sh] = 0;

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
-sum {t in time, (l,n,m) in branch: Scond[t,l,n,m]}      Sl_max[l]*lambda13[t,l,n,m]

-penalty*(
sum {t in time, g in gen} (c2[g]*Pgen[t,g]^2 + c1[g]*Pgen[t,g] + c0[g])

-(
-sum {t in time, es in es_bus}							 qbat[t]*lambda1es_param[t]
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
-sum {t in time, (l,n,m) in branch: Scond[t,l,n,m]}      Sl_max[l]*lambda13[t,l,n,m]
)

);