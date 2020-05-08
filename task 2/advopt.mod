set P; #Places
set T := 0..48; #time intervals
set L := 12..16; #Lunch time
set D := 36..40; #Dinner time
set F := 8..28; #Forbidden time for outdoor 
set R; #Restaurants
#set A; #Attractions
set H; #Hotel
set RA;
set LD := L union D; #Lunch and Dinner time

set NLD :=  T diff ( L union D );


param o{P}; #1 for outdoor attraction
param c{P}; #Cost of attraction
param p{P};  #processing time of place, 2 for attraction and 4 for restaurant
param u{P, P}; #cost of travelling between each place
param d{P, P}; #time to travel between each place
param W{P}; #1 if place is in the west
param E{P}; #1 if place is in the east
param N{P}; #1 if place is in the north
param S{P}; #1 if place is in the north-east
#param h{P}; #1 if place is a hotel

param A{P}; # Indiacator of place is attraction
var x{P,T} binary; #1 if visitor arrives at place i at time t
var e{P,P} binary; #1 if transportation takes place from i to j
var K{P} binary; #Dummy variable
var delW binary; #Dummy variable to count if West is visited
var delE binary; #Dummy variable to count if East is visited
var delS binary; #Dummy variable to count if South is visited
var delN binary; #Dummy variable to count if North is visited
#	sum{i in P, j in P: i != j} e[i,j]*(u[i,j] + (c[i] + c[j])/2 );
minimize total_cost: #transportation cost + attraction cost 
	sum{i in P, j in P: i != j} e[i,j]*u[i,j] + sum{i in P, t in T} x[i,t]*c[i];
	

subject to C2{i in P}: # Every node is either in the cycle or not
	(sum{j in P: j!=i} e[i,j]) +(sum {k in P: k!=i}  e[k,i]) = 2*K[i];

subject to C3{i in P}: # A place can only go to at most one anohter place
	sum{j in P: j != i}  e[i,j] <=1;
	

subject to C4{i in P}: # A palce can be visted  at most once
	sum {j in P: j != i} e[j, i]<= 1;
	
subject to C19{i in P, j in P: j!= i}: 
	sum{t in T} x[i,t] + sum{f in T} x[j,f] >= 2*e[i,j];

subject to C20 {i in P: i not in H}:
	sum{t in T} x[i,t] <=1;

subject to C21 {i in P}:
	sum{j in P: j != i} e[i,j] = sum{t in T:t>0} x[i,t];
	
subject to C100{t in T}:
	sum{i in P: i not in H} x[i,t] <= 1;

subject to C99:
	 x["H1",0]=1;
	
subject to C150:
	sum{t in T} x["H1",t]=2;

subject to C151{i in P: i not in H}:
	sum{t in T} x[i,t]*  t<= sum {f in T}x["H1",f]*f ;
	
# rmb to fucking exclude hotel from this set
subject to C98{i in P, j in P: j != i and (i not in H) and (j not in H)}:
	2000*(1-e[i,j]) >= (sum{t in T} t*x[i,t])+p[i]+d[i,j] - (sum{f in T} f*x[j,f]);	

subject to C171{j in P: j not in H}:
	2000*(1-e["H1",j]) >= d["H1", j] - sum{t in T: t>0} x[j,t]*t;

subject to C172{i in P: i not in H}:
	2000*(1-e[i,"H1"]) >= (sum{t in T:t>0} t*x[i,t])+p[i]+d[i,"H1"] - 48;

#subject to C6: #hotel is the inside cycle
#		sum{i in H,j in P: j!= i} e[i,j] = 1;

#subject to C7:
#		sum{i in H,j in P: j!= i} e[j, i] = 1;
	

subject to C5: # total span 
	sum{i in P, j in P: j!=i} e[i,j]* (d[i,j] + p[i]) <= 48;

subject to C8: # at least 8 attractions are visited 
		sum{i in P, j in P: j!= i} e[i,j]*A[i] >=8;
		
subject to C9: # at least three are outdoors
	sum{i in P, j in P: j!=i }e[i,j]*o[i] >=3;

subject to C10:
	sum{i in P, j in P: j!= i} e[i,j]*W[i] <= 500*delW;

subject to C11:
	sum{i in P, j in P: j!= i} e[i,j]*W[i] >= 1 - 500*delW;

subject to C12:
	sum{i in P, j in P: j!= i} e[i,j]*E[i] <= 500*delE;

subject to C13:
	sum{i in P, j in P: j!= i} e[i,j]*E[i] >= 1 - 500*delE;

subject to C14:
	sum{i in P, j in P: j!= i} e[i,j]*N[i] <= 500*delN;

subject to C15:
	sum{i in P, j in P: j!= i} e[i,j]*N[i] >= 1 - 500*delN;
	
subject to C16:
	sum{i in P, j in P: j!= i} e[i,j]*S[i] <= 500*delS;

subject to C17:
	sum{i in P, j in P: j!= i} e[i,j]*S[i] >= 1 - 500*delS;
	
subject to C18:
	delW + delE + delN + delS >= 2;
	
subject to C80:
	sum{t in L, i in R} x[i,t]=1;

subject to C55:
 	sum{f in D, i in R} x[i,f]=1;

subject to C {i in R, t in NLD}:
 		x[i,t] =0;
 		
#subject to C1000{i in P, t in F}:
# 	sum{i in P, t in F} A[i]*x[i,t]*o[i] =0;
 	
subject to C1000{i in P, t in F}:
		 A[i]*x[i,t]*o[i] =0;