#define N 4
#define L 10

chan q[N] = [L] of { byte };

byte nr_leaders = 0;

#define noLeaderYet (nr_leaders == 0)
#define leaderIsElected (nr_leaders > 0)
#define exactlyOneLeaderElected (nr_leaders == 1)

proctype node(chan in, out; byte ident) {
  byte d,e,f, max;

  activ:
    d = ident;
    do
      :: true ->
        atomic {
          out!d;
          in?e;
          if
            :: (e == d) -> 
                nr_leaders++;
                goto stop
            :: skip
          fi
          out!e;
          in?f;
          max = (d >= f -> d : f)
          if
            :: (e >= max) -> d = e
            :: else -> goto relay 
          fi
        }
    od

    relay:
      do
        :: true ->
          in?d;
          out!d;
      od

    stop:
      skip;
      
}

// #define I 152 //possible smaller identifier
init {
  byte i;
  byte Ident[N];
  
  /*
  atomic { //assign identifiers to processes
    //for i from 0 to N-1
    for (i : 0 .. N - 1) {
      Ident[i]=(N+I-i-1)%N+1;
    }
  }
  */
  
  atomic {
    Ident[0] = 4;
    Ident[1] = 27;
    Ident[2] = 3;
    Ident[3] = 121;
  }
  
  // for i from 1 to N
  atomic {
    for (i : 1 .. N) {
        run node(q[i-1],q[i%N],Ident[i-1])
    }
  }
}

ltl OnlyOneLeader { []( nr_leaders == 0 || nr_leaders == 1) }
ltl AlwaysAtMostOneLeader { [](noLeaderYet || (leaderIsElected && exactlyOneLeaderElected)) }
ltl AlwaysALeaderElectedEventually{ <>[] leaderIsElected}
ltl NoLeaderUntilElected { noLeaderYet U leaderIsElected}