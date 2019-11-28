mtype = {red, green, yellow, b2}


byte state = red
active proctype P1() {

  do
    :: (state == green) -> state = yellow;
    :: (state == yellow) -> state = red;
    :: (state == yellow) -> state = b2;
    :: (state == b2) -> state = yellow;
    :: (state == red) -> state = green;
//    printf(state);
  od  
}

ltl Cond1 { <>state == green  }
ltl Cond2 { []state == green || state == red || state == yellow || state == b2  }
ltl Cond3 { state == yellow -> <> state == red  }
