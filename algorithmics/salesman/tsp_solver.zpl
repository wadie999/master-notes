set Villes := {read "tsp50.txt" as "<1n>" skip 1, <0>};
param coX[Villes] := read "tsp50.txt" as "<1n> 2n" skip 1, <0> 0;
param coY[Villes] := read "tsp50.txt" as "<1n> 3n" skip 1, <0> 0;

var x_ij[Villes * Villes] binary;
var u[Villes] integer;

# Calculate Euclidean distance for each pair of cities
defnumb dist_euclidean(i, j) := sqrt((coX[i] - coX[j])^2 + (coY[i] - coY[j])^2);

minimize Total_Distance:
  sum <i, j> in Villes cross Villes with i != j: dist_euclidean(i,j) * x_ij[i,j];



#Constraint: Enter Each City Once
subto EnterOnce:
  forall <i> in Villes:
    sum <j> in Villes with i != j: x_ij[i,j] == 1;



#Constraint: Leave Each City Once
subto LeaveOnce:
  forall <j> in Villes:
    sum <i> in Villes with i != j: x_ij[i,j] == 1;


#This constraint prevents the formation of subtours, which are smaller loops within the tour that don't include all cities.
subto NoSubtour:
  forall <i, j> in Villes cross Villes with i != 1 and j != 1 and i != j do
    u[i] - u[j] + card(Villes) * x_ij[i,j] <= card(Villes) - 1;
