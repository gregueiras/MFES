//Two traffic-lights at an intersection
//MFES 2019-20
mtype = {red, yellow, green};
// needs to start
bit turn = 0;
mtype light[2]= {red,red};
//two idenical processes start
//processes id are 0 and 1
active [2] proctype P() {
// _pid process id
bit myId = _pid;
bit otherId = 1 - _pid;
do
:: turn == myId && light[myId] == red
-> light[myId] = green
:: light[myId] == green
-> light[myId] = yellow
:: light[myId] == yellow
-> light[myId] = red; turn = otherId
od
}
ltl P0 {[]!( (light[0] == green) && (light[1] == green))}
ltl P1 {([] <> (light[0]==green)) && ([] <> (light[1]==green)) }