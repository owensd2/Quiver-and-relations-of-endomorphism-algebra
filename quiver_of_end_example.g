Read("quiver_of_end.g");

K := Rationals; 
Q := Quiver(1,[[1,1,"a"],[1,1,"b"]]);
KQ := PathAlgebra(K,Q);

AssignGeneratorVariables(KQ);
rel := [a^2, a*b+b^2+b^2*a];
A := KQ/rel;
Dimension(A);
IsSelfinjectiveAlgebra(A);

RegA := DirectSumOfQPAModules(IndecProjectiveModules(A));
CoRegA := DirectSumOfQPAModules(IndecInjectiveModules(A));
U1 := DTr(NthSyzygy(CoRegA,1));
U2 := DTr(NthSyzygy(U1,1));
U3 := DTr(NthSyzygy(U2,1));
U4 := DTr(NthSyzygy(U3,1));

IsProjectiveModule(U4);

ExtOverAlgebra(CoRegA,RegA);

M := DirectSumOfQPAModules([CoRegA,U1,U2,U3,U4]);

B := QuiverAndRelationsOfEndOfModule(M,20);

vertex_module_list := B[5];
# e.g. module at v1
vertex_module_list[1];

GlobalDimensionOfAlgebra(B[1],3);
DominantDimensionOfAlgebra(B[1],3);
