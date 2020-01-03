mtype = { red, green, yellow }

bit turn = 0
mtype light[2]= { red, red };

#define g0 light[0] == green
#define g1 light[1] == green


active [2] proctype trafficLigth() {
  // _pid  process id
  bit myId = _pid; 
  bit otherId = 1 - _pid;

  do
      :: (myId == turn && light[myId] == red) ->   
            light[myId] = green

      :: (light[myId] == green) ->
            light[myId] = yellow

      :: (light[myId] == yellow) ->
            light[myId] = red;
            turn = otherId;
  od
}

//ltl C1 { []((g0 -> !g1) && (g1 -> !g0)) }
ltl C1 { []! (g0 && g1) }
ltl C2 { (([]<> (g0)) && ([]<> (g1))) }

ltl P0 {[]!( (light[0] == green) && (light[1] == green))}
ltl P1 {([] <> (light[0]==green)) && ([] <> (light[1]==green)) }