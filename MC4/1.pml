mtype = { msg0, msg1, ack0, ack1 };
chan sender = [1] of { mtype };
chan receiver = [1] of { mtype };

#define smsg0 (receiver?[msg0])
#define smsg1 (receiver?[msg1])
#define rmsg0 (sender?[ack0])
#define rmsg1 (sender?[ack1])
#define srmsg0 Sender@send0
#define srmsg1 Sender@send1
#define send (srmsg0 || srmsg1)

active proctype Sender()
{
  do
  ::
    if
    :: receiver?msg0;
    :: skip
    fi;
    do
      :: sender?ack0 -> break
      :: sender?ack1
      :: timeout ->
         if
        ::
        receiver!msg0;
        send0: :: skip
        fi;
    od;
    ::
      if
      :: receiver?msg1;
      :: skip
      fi;
      do
      :: sender?ack1 -> break
      :: sender?ack0
      :: timeout ->
       if
        ::
        receiver!msg1;
       send1: :: skip
        fi;
      od;
  od;
}

active proctype Receiver()
{
  do
    ::
    do
    :: receiver?msg0 ->
      sender!ack0; break
    :: receiver?msg1 ->
      sender!ack1
    od;
    do
    :: receiver?msg1 ->
      sender!ack1; break
    :: receiver?msg0 ->
      sender!ack0
    od
  od
}

ltl CorrectResponse0 { [](smsg0 -> (<>smsg1)) }
ltl CorrectResponse1 { [](smsg1 -> (<>smsg0)) }
ltl InfAck0 { []<>((smsg0) -> (<>[] rmsg0)) }
ltl InfAck1 { []<>((smsg1) -> (<>[] rmsg1)) }

ltl f1_0 { [](smsg0 -> (smsg0 U (! smsg0 && (! smsg0 U rmsg0)))) }
ltl f1_1 { [](smsg1 -> (smsg1 U (! smsg1 && (! smsg1 U rmsg1)))) }

ltl f2 { [](srmsg0 -> (send U (! send && (! send U smsg0)))) }
ltl f3 { [](srmsg1 -> (send U (! send && (! send U smsg1)))) }
