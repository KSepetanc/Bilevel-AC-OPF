var fi   {time, bus};
var V    {time, n in bus} := 1;
var P    {time, (l,n,m) in branch};
var Q    {time, (l,n,m) in branch};
var Pgen {time, g in gen};
var Qgen {time, g in gen};

minimize QPOF: sum {t in time, g in gen} (c2[g]*Pgen[t,g]^2 + c1[g]*Pgen[t,g] + c0[g]);

subject to bus_p_pol {t in time, n in bus}:
 sum {(n,g) in bus_gen} Pgen[t,g] - sum {(n,lo) in bus_load} pd[lo]*load_f[t] 
-sum {(l,n,m) in branch} P[t,l,n,m] - sum{(n,sh) in bus_shunt} V[t,n]^2*gs[sh]
- (if n in es_bus then qbat_fix[t]) = 0;

subject to bus_q_pol {t in time, n in bus}:
 sum {(n,g) in bus_gen} Qgen[t,g] - sum {(n,lo) in bus_load} qd[lo]*load_f[t] 
-sum {(l,n,m) in branch} Q[t,l,n,m] + sum{(n,sh) in bus_shunt} V[t,n]^2*bs[sh] 
- (if n in es_bus then qqbat_fix[t]) = 0;

subject to power_f_pol {t in time, (l,n,m) in branch_from}:
 P[t,l,n,m] = V[t,n]^2*(gl[l]+gl_fr[l])/tap[l]^2 
 			- V[t,n]*V[t,m]*(gl[l]*cos(fi[t,n]-fi[t,m]-shift[l]) + bl[l]*sin(fi[t,n]-fi[t,m]-shift[l]))/tap[l];
 
subject to power_t_pol {t in time, (l,n,m) in branch_to}:
 P[t,l,n,m] = V[t,n]^2*(gl[l]+gl_to[l])
 			- V[t,n]*V[t,m]*(gl[l]*cos(fi[t,n]-fi[t,m]+shift[l]) + bl[l]*sin(fi[t,n]-fi[t,m]+shift[l]))/tap[l];
 			
subject to reactive_f_pol {t in time, (l,n,m) in branch_from}:
 Q[t,l,n,m] =-V[t,n]^2*(bl[l]+bl_fr[l])/tap[l]^2 
 			- V[t,n]*V[t,m]*(gl[l]*sin(fi[t,n]-fi[t,m]-shift[l]) - bl[l]*cos(fi[t,n]-fi[t,m]-shift[l]))/tap[l];
 			
subject to reactive_t_pol {t in time, (l,n,m) in branch_to}:
 Q[t,l,n,m] =-V[t,n]^2*(bl[l]+bl_to[l])
 			- V[t,n]*V[t,m]*(gl[l]*sin(fi[t,n]-fi[t,m]+shift[l]) - bl[l]*cos(fi[t,n]-fi[t,m]+shift[l]))/tap[l];
 			
subject to linemax_pol {t in time, (l,n,m) in branch}:
 P[t,l,n,m]^2 + Q[t,l,n,m]^2 <= Sl_max[l]^2;
 
subject to volt12_pol {t in time, n in bus}:
 vmin[n] <= V[t,n] <= vmax[n];

subject to pg12 {t in time, g in gen}:
 pg_min[g] <= Pgen[t,g] <= pg_max[g];

subject to qg12 {t in time, g in gen}:
 qg_min[g] <= Qgen[t,g] <= qg_max[g];

subject to refc_pol {t in time, n in refbus}:
 fi[t,n] = 0;