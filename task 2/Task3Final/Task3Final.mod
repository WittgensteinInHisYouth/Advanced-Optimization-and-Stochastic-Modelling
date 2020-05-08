set P; #Places
set T := 0..48; #time intervals for Day 1
set T2:= 49..97; #time interval for Day 2
set Tall:= 0..97; #time interval for two days
set L := 8..20; #Day 1 Lunch time
set D := 32..44; #Day 2 Dinner time

set L2 := 56..68; #Day 1 Lunch time
set D2 := 80..92; #Day 2 Dinner time
 
set R; #Restaurants
set H; #Hotel
#Replace H(number) as necessary according to simulated annealing
set RA; #Restaurants and attractions
set LD := L union D; #Day 1 Lunch and Dinner time
set LD2 := L2 union D2; #Day 2 Lunch and Dinner time
set NLD :=  T diff ( L union D ); #Day 1 non Lunch and Dinner time
set NLD2 :=  T2 diff ( L2 union D2 ); #Day 2 non Lunch and Dinner time

param o{P}; #1 for outdoor attraction
param c{P}; #Cost of attraction
param p{P};  #processing time of place, 2 for attraction and 4 for restaurant
param u{P, P}; #cost of travelling between each place
param d{P, P}; #time to travel between each place
param W{P}; #1 if place is in the west
param E{P}; #1 if place is in the east
param N{P}; #1 if place is in the north
param S{P}; #1 if place is in the north-east
param C{P}; #1 if place is in the center
param A{P}; # Indiacator of place is attraction

var x{P,Tall} binary; #1 if visitor arrives at place i at time t
var e{P,P} binary; #1 if transportation takes place from i to j on Day 1
var l{P,P} binary; #1 if transportation takes place from i to j on day 2
var K{P} binary; #Dummy variable
var J{P} binary; #Dummy variable
var delW binary; #Dummy variable to count if West is visited
var delE binary; #Dummy variable to count if East is visited
var delS binary; #Dummy variable to count if South is visited
var delN binary; #Dummy variable to count if North is visited
var delC binary; #Dummy variable to count if Center is visited

minimize diff_diversity: #Difference between outdoor and indoor attractions 
	sum{i in P, j in P: i != j} (e[i,j]+l[i,j])*o[i]*A[i] - sum{i in P, j in P: i != j} (e[i,j]+l[i,j])*(1-o[i])*A[i];

subject to C0: #Number of outdoor attractions visited needs to be more than the indoor attractions visited
	sum{i in P, j in P: i != j} (e[i,j]+l[i,j])*o[i]*A[i] >= sum{i in P, j in P: i != j} (e[i,j]+l[i,j])*(1-o[i])*A[i];

subject to C1{i in P}: #Every node is either in the cycle or not on Day 1
	(sum{j in P: j!=i} e[i,j]) +(sum {k in P: k!=i}  e[k,i]) = 2*K[i];
	
subject to C1day2{i in P}: #Every node is either in the cycle or not on Day 2
	(sum{j in P: j!=i} l[i,j]) +(sum {k in P: k!=i}  l[k,i]) = 2*J[i];

subject to C2{i in P}: #A place can only go to at mosst one another place on Day 1
	sum{j in P: j != i}  e[i,j] <=1;

subject to C2day2{i in P}: #A place can only go to at most one another place on Day 2
	sum{j in P: j != i}  l[i,j] <=1;
	
subject to C3{i in P}: #A place can be visted at most once on Day 1
	sum {j in P: j != i} e[j, i]<= 1;

subject to C3day2{i in P}: #A place can be visted at most once on Day 2
	sum {j in P: j != i} l[j, i]<= 1;
	
subject to C4{i in P, j in P: j!= i}: #If there is an edge between two places, they must be visited sometime on Day 1
	sum{t in T} x[i,t] + sum{f in T} x[j,f] >= 2*e[i,j];

subject to C4day2{i in P, j in P: j!= i}: #If there is an edge between two places, they must be visited sometime on Day 2
	sum{t in T2} x[i,t] + sum{f in T2} x[j,f] >= 2*l[i,j];

subject to C5 {i in P: i not in H}: #Each restaurant and attraction is visited at most once
	sum{t in Tall} x[i,t] <=1;

subject to C6 {i in P}: 
	sum{j in P: j != i} e[i,j] = sum{t in T:t>0} x[i,t];

subject to C6day2 {i in P}:
	sum{j in P: j != i} l[i,j] = sum{t in T2:t>49} x[i,t];
	
subject to C7{t in Tall}: #At a time instant only one place can be visited
	sum{i in P} x[i,t] <= 1;

subject to C8: #Start from one hotel on Day 1
	 x["H5",0]=1;
	 
subject to C8day2: #Start from hotel on Day 2
	 x["H5",49]=1;
	
subject to C9: #On Day 2 hotel is visited twice
	sum{t in T} x["H5",t]=2;
	
subject to C9day2: #On day 2 hotel is visited twice
	sum{t in T2} x["H5",t]=2;

subject to C10{i in P: i not in H}: #The last place we go on Day 1 is the hotel
	sum{t in T} x[i,t]*  t<= sum {f in T:f>0}x["H5",f]*f ;

subject to C10day2{i in P: i not in H}: #The last place we go on Day 2 is the hotel
	sum{t in T2} x[i,t]*  t<= sum {f in T2:f>49}x["H5",f]*f ;
	
subject to C11{i in P, j in P: j != i and (i not in H) and (j not in H)}: #On Day 1 if j is after i, then the duration between start time of i and j should be greater or equal to the process time and the transportation time
	2000*(1-e[i,j]) >= (sum{t in T} t*x[i,t])+p[i]+d[i,j] - (sum{f in T} f*x[j,f]);	
	
subject to C11day2{i in P, j in P: j != i and (i not in H) and (j not in H)}: #On Day 2 if j is after i, then the duration between start time of i and j should be greater or equal to the process time and the transportation time
	2000*(1-l[i,j]) >= (sum{t in T2} t*x[i,t])+p[i]+d[i,j] - (sum{f in T2} f*x[j,f]);	

subject to C12{j in P: j not in H}: 
	2000*(1-e["H5",j]) >= d["H5", j] - sum{t in T: t>0} x[j,t]*t;

subject to C12day2{j in P: j not in H}:
	2000*(1-l["H5",j]) >= 49 + d["H5", j] - sum{t in T2: t>0} x[j,t]*t;

subject to C13{i in P: i not in H}:
	2000*(1-e[i,"H5"]) >= (sum{t in T:t>0} t*x[i,t])+p[i]+d[i,"H5"] - 48;
	
subject to C13day2{i in P: i not in H}:
	2000*(1-l[i,"H5"]) >= (sum{t in T2:t>0} t*x[i,t])+p[i]+d[i,"H5"] - 97;

subject to C14: #Hotel is inside the cycle for Day 1
		sum{i in H,j in P: j!= i} e[i,j] = 1;

subject to C14day2: #Hotel is inside the cycle for Day 2
		sum{i in H,j in P: j!= i} l[i,j] = 1;

subject to C15: #Hotel is inside the cycle for Day 1
		sum{i in H,j in P: j!= i} e[j, i] = 1;
	
subject to C15day2: #Hotel is inside the cycle for Day 2
		sum{i in H,j in P: j!= i} l[j, i] = 1;

subject to C16: #Total span for Day 2 cannot exceed Day 1
	sum{i in P, j in P: j!=i} e[i,j]* (d[i,j] + p[i]) <= 48;

subject to C16day2: #Total span for day 2 cannot exceed Day 2 
	sum{i in P, j in P: j!=i} l[i,j]* (d[i,j] + p[i]) <= 48;

subject to C17: #Indicator if West is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*W[i] <= 500*delW;

subject to C18: #Indicator if West is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*W[i] >= 1 - 500*delW;

subject to C19: #Indicator if East is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*E[i] <= 500*delE;

subject to C20: #Indicator if East is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*E[i] >= 1 - 500*delE;

subject to C21: #Indicator if North is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*N[i] <= 500*delN;

subject to C22: #Indicator if North is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*N[i] >= 1 - 500*delN;
	
subject to C23: #Indicator if North-East is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*S[i] <= 500*delS;

subject to C24: #Indicator if North-East is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*S[i] >= 1 - 500*delS;

subject to Center1: #Indicator if Central is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*C[i] <= 500*delC;

subject to Center2: #Indicator if Central is visited
	sum{i in P, j in P: j!= i} (e[i,j]+l[i,j])*C[i] >= 1 - 500*delC;

subject to C25: #Regions visited must be more than 3
	delW + delE + delN + delS + delC>= 3;
	
subject to C26: #Only one restaurant is visited during lunch for Day 1
	sum{t in L, i in R} x[i,t]=1;

subject to C26day2: #Only one restaurant is visited during lunch for Day 2
	sum{t in L2, i in R} x[i,t]=1;

subject to C27: #Only one restaurant is visited during dinner for Day 1
 	sum{f in D, i in R} x[i,f]=1;
 	
 subject to C27day2: #Only one restaurant is visited during dinner for Day 2
 	sum{f in D2, i in R} x[i,f]=1;

subject to C28 {i in R, t in NLD}: #No restaurants visited when it is not lunch or dinner time on Day 1
 		x[i,t] =0;
 
subject to C28day2 {i in R, t in NLD2}: #No restaurants visited when it is not lunch or dinner time on Day 2
 		x[i,t] =0;

subject to C29: #At least 3 outdoor attractions must be visited on Day 1
		sum{i in P, j in P: j!= i}   e[i,j]*o[i]*A[i] >=3;
		
subject to C29day2: #At least 3 outdoor attractions must be visited on Day 2
		sum{i in P, j in P: j!= i}  l[i,j]*o[i]*A[i]>=3;
		
subject to C30: #At most 7 outdoor attractions must be visited on Day 1
		sum{i in P, j in P: j!= i}  e[i,j]*o[i]*A[i] <=7;
		
subject to C30day2: #At most 7 outdoor attractions must be visited on Day 2
		sum{i in P, j in P: j!= i}  l[i,j]*o[i]*A[i] <=7;

subject to C31: #At least 2 indoor attractions must be visited on Day 1
		sum{i in P, j in P: j!= i}   e[i,j]* (1-o[i])*A[i] >=2;
		
subject to C31day2: #At least 2 indoor attractions must be visited on Day 2
		sum{i in P, j in P: j!= i}  l[i,j]*(1-o[i])*A[i]>=2;
		
subject to C32: #At most 5 indoor attractions must be visited on Day 1
		sum{i in P, j in P: j!= i}  e[i,j]*(1-o[i])*A[i] <=5;
		
subject to C32day2: #At most 5 indoor attractions must be visited on Day 2
		sum{i in P, j in P: j!= i}  l[i,j]*(1-o[i])*A[i] <=5;

subject to C33{i in P}: #All the attractions are visited only once
	sum{t in Tall} x[i,t]*A[i]<=1;
	
subject to budget: #Budget constraints to modify as necessary
	sum{i in P, j in P: i != j} (e[i,j]+l[i,j])*u[i,j] + sum{i in P, t in Tall} x[i,t]*c[i] <= 180;