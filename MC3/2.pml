

bit b[2] = {true, false}
bit c[2] = {false, false}
bit x = 1

#define crit0 c[0]
#define crit1 c[1]

#define wants0 (x == 1 || !b[1])
#define wants1 (x == 0 || !b[0])

active [2] proctype P() {

  bit myTurn = _pid;
  bit otherTurn = 1 - _pid;

  do
    :: true -> 
      skip;

      // non critical zone
      atomic {
        b[myTurn] = true;
        x = myTurn;
      }

      if :: (x == otherTurn || !b[otherTurn]) ->
          // process myTurn entered critical zone
          c[myTurn] = true
      fi

      // exit critical zone
      atomic {
        b[myTurn] = false;
        c[myTurn] = false;
      }  
  od
} 

ltl P1 { []!(crit0 && crit1) }
ltl P2 { ([]<> (crit0)) && ([]<> (crit1)) }
ltl P3 { [](wants0 -> <>crit0) && [](wants1 -> <>crit1)}
ltl P4 { ([]<> wants0 -> []<>crit0) && ([]<> wants1 -> []<> crit1)}