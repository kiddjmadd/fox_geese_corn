include "globals.mzn";

int: f;
int: g;
int: c;
int: k;
set of int: Cap = 0..k;
int: t;
set of int: Trips = 1..t+1;
set of int: Trips0 = 1..t;
int: pf;
int: pg;
int: pc;

set of int: MaxGoods = 0..f+g+c;

array[Trips,1..3,0..1] of var MaxGoods: Shore; % time t, f,g,c, west/east

array[Trips] of var MaxGoods: westContents;
array[Trips0] of var Cap: fox;
array[Trips0] of var Cap: geese;
array[Trips0] of var Cap: corn;
var 1..t: trips;
array[Trips] of var bool: CurrSide;

var 0..f*pf+g*pg+c*pc: obj;

function var int: consume_unatt_fox(var int: uf, var int: ug, var int: uc, var int: wc) =
    (bool2int(uf > 0 /\ ug == 0 /\ uc > 0) + bool2int(uf >0 /\ ug > 0 /\ uf > ug))*bool2int(wc>0)
;
function var int: consume_unatt_goose(var int: uf, var int: ug, var int: uc, var int: wc) =
    (bool2int(uf == 0 /\ ug > 0 /\ uc > 0 /\ ug > uc) + bool2int(uf > 0 /\ ug > 0 /\ uf <= ug)*uf)*bool2int(wc>0)
;
function var int: consume_unatt_corn(var int: uf, var int: ug, var int: uc, var int: wc) =
    (bool2int(uf > 0 /\ ug == 0 /\ uc > 0) + bool2int(uf == 0 /\ ug > 0 /\ uc > 0 /\ ug > uc) + bool2int(uf == 0 /\ ug > 0 /\ uc > 0 /\ ug <= uc)*ug)*bool2int(wc>0)
;

predicate process_moves(var int: opp_prev_fox, var int: opp_prev_goose, var int: opp_prev_corn, var int: opp_curr_fox, 
                        var int: opp_curr_goose, var int: opp_curr_corn, var int: same_prev_fox, var int: same_prev_goose, 
                        var int: same_prev_corn, var int: same_curr_fox, var int: same_curr_goose, var int: same_curr_corn,
                        var Cap: boat_prev_fox, var Cap: boat_prev_goose, var Cap: boat_prev_corn, 
                        var Cap: boat_curr_fox, var Cap: boat_curr_goose, var Cap: boat_curr_corn, var int: wc) =
    (same_curr_fox = same_prev_fox + boat_prev_fox /\
    same_curr_goose = same_prev_goose + boat_prev_goose /\
    same_curr_corn = same_prev_corn + boat_prev_corn  /\
    opp_curr_fox = opp_prev_fox - boat_prev_fox - consume_unatt_fox(opp_prev_fox-boat_prev_fox, opp_prev_goose-boat_prev_goose, opp_prev_corn-boat_prev_corn,wc)/\
    opp_curr_goose = opp_prev_goose - boat_prev_goose  - consume_unatt_goose(opp_prev_fox-boat_prev_fox, opp_prev_goose-boat_prev_goose, opp_prev_corn-boat_prev_corn,wc) /\
    opp_curr_corn = opp_prev_corn - boat_prev_corn  - consume_unatt_corn(opp_prev_fox-boat_prev_fox, opp_prev_goose-boat_prev_goose, opp_prev_corn-boat_prev_corn,wc))  
    ;


%%%%%%%%%%%%%%%%%%%%%%%%%%% ADD constraints in here %%%%%%%%%%%%%

% Initialize contents of West (we'll call West zero):

constraint Shore[1,1,0]=f;
constraint Shore[1,2,0]=g;
constraint Shore[1,3,0]=c;

% Initialize contents of East:
constraint Shore[1,1,1]=0;
constraint Shore[1,2,1]=0;
constraint Shore[1,3,1]=0;

% define westContents utility variable:
constraint forall (i in Trips)(westContents[i] = sum(j in 1..3)(Shore[i,j,0]));

% Boat is limited by capacity for all trips
constraint forall(i in Trips0)(fox[i] + geese[i] + corn[i] <= k /\ fox[i] >=0 /\ geese[i] >=0 /\ corn[i] >=0);

% Boat can't take more than is there.
constraint forall(i in Trips0) (fox[i] <= Shore[i,3,CurrSide[i]] /\ geese[i] <= Shore[i,2,CurrSide[i]] /\ corn[i] <= Shore[i,3,CurrSide[i]]);

% No negative quantities:
constraint forall(i in Trips, j in 1..3, k in 0..1)(Shore[i,j,k]>=0); % Should also keep 'selected' items in check.

% Define CurrSide:
constraint forall(i in Trips)(CurrSide[i]= (i mod 2==0));

% define trips as first t where west side is empty
constraint trips = sum(i in Trips)(bool2int(westContents[i] > 0));
%constraint forall(i in 1..3) (Shore[trips+1,i,0]=0);
%constraint trips+1 <= t;
constraint Shore[t+1,1,0]=0/\Shore[t+1,2,0]=0/\Shore[t+1,3,0]=0;
constraint obj = (Shore[t,1,1]*pf+Shore[t,2,1]*pg+Shore[t,3,1]*pc); % calculate profit at t

% constraint forall(trip in Trips where Shore[trip,1,0]==0 /\ Shore[trip,2,0]==0 /\ Shore[trip,3,0]==0)
%         (fox[trip]=0 /\ geese[trip]=0 /\ corn[trip]=0);

%constraint forall(trip in Trips, i in 1..3, j in 0..1 where Shore[trip,1,0]==0 /\ Shore[trip,2,0]==0 /\ Shore[trip,3,0]==0) 
%    (Shore[trip,i,j] = Shore[trip-1,i,j]);
    

constraint forall(trip in Trips where trip >1 /\ trip <= t)(process_moves(Shore[trip-1,1,not CurrSide[trip]],Shore[trip-1,2,not CurrSide[trip]],Shore[trip-1,3,not CurrSide[trip]],
                   Shore[trip,1,not CurrSide[trip]],Shore[trip,2,not CurrSide[trip]],Shore[trip,3, not CurrSide[trip]], 
                   Shore[trip-1,1,CurrSide[trip]],Shore[trip-1,2,CurrSide[trip]],Shore[trip-1,3,CurrSide[trip]],
                   Shore[trip,1,CurrSide[trip]],Shore[trip,2,CurrSide[trip]],Shore[trip,3,CurrSide[trip]],
                   fox[trip-1], geese[trip-1], corn[trip-1],fox[trip], geese[trip], corn[trip],westContents[trip]));


%%%%%%%%%%%%%%%%% you may want to modify the search strategy below
%solve maximize obj;
solve :: int_search([trips], input_order, indomain_min, complete) maximize obj;
%solve :: int_search([trips], input_order, indomain_min, complete) minimize trips;



output ["  fox = ", show(fox),
     ";\ngeese = ", show(geese),
     ";\n corn = ", show(corn),
     ";\ntrips = ", show(trips), 
     ";\n  obj = ", show(obj),

%     ";\n  westContents = ", show(westContents),
%     ";\n  CurrSide = ", show(CurrSide),
%     ";\n"] ++ 
%     [show (Shore[i,j,k]) ++ if j==3 /\ k ==1 then " \n" elseif k==1 then " \t" else " " endif | i in Trips, j in 1..3, k in 0..1]; % Comment me out! 

     ";\n"];
