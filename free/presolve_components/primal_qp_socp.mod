var cv1 {time, buspair};
var cv2 {time, buspair}     := 1/4;
var cv3 {time, buspair}     := 1/4, >= 0;
var v1  {time, branch_from} := 1/2;
var v2  {time, branch_from};
var v3  {time, branch_from};
var v4  {time, branch_from} := 1/2, >= 0;

subject to cos0 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
 cv1[t,n,m]^2 + cv2[t,n,m]^2 <= cv3[t,n,m]^2;

subject to cos1 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
 cv1[t,n,m] = dfi[t,n]/sqrt(2) - dfi[t,m]/sqrt(2);
 
subject to cos2 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
 cv2[t,n,m] = cos_f[t,n,m] - 3/4;

subject to cos3 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
 cv3[t,n,m] = -cos_f[t,n,m] + 5/4;

#subject to cos2 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
# cv2[t,n,m] = cos_f[t,n,m]/2;

#subject to cos3 {t in time, (n,m) in buspair: Ccond[t,n,m]}:
# cv3[t,n,m] = -cos_f[t,n,m]/2 + 1;

subject to cos00 {t in time, (n,m) in buspair: !Ccond[t,n,m]}:
 cos_f[t,n,m] = 1;


subject to v_soa0 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
 v1[t,l,n,m]^2 + v2[t,l,n,m]^2 + v3[t,l,n,m]^2 <= v4[t,l,n,m]^2;

subject to v_soa1 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
 v1[t,l,n,m] = -v_soa[t,l]/2 + 1/2;

subject to v_soa2 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
 v2[t,l,n,m] = vm1[t,l,n,m]*dV[t,n] - vm2[l]*dV[t,m];

subject to v_soa3 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
 v3[t,l,n,m] = vm3[t,l,n,m]*dV[t,n];

subject to v_soa4 {t in time, (l,n,m) in branch_from: Vcond[t,l,n,m]}:
 v4[t,l,n,m] = v_soa[t,l]/2 + 1/2;

subject to v_soa00 {t in time, (l,n,m) in branch_from: !Vcond[t,l,n,m]}:
 v_soa[t,l] = 0;