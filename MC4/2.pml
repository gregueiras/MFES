//floor indicates which floor the elevator is
byte floor=1;
//doorisopen[i]==1 if the door of floor i is open
bit doorisopen[3];
//rendezvous between the cabin and the floor door:byte is the floor number and
// bit is 1 if the door is open, and 0 if it is closed
chan openclosedoor=[0] of {byte,bit};


#define open1 doorisopen[1]
#define open2 doorisopen[2]
#define open3 doorisopen[3]

#define close1 !doorisopen[1]
#define close2 !doorisopen[2]
#define close3 !doorisopen[3]

#define open (open1 || open2 || open3 )
#define close (close1 || close2 || close3 )

#define floor1 (floor == 1)
#define floor2 (floor == 2)
#define floor3 (floor == 3)

#define moving (elevator@moveUp || elevator@moveDown)


proctype door(byte i){
//waits for elevator to allow door open in floor i
//opens the door (bit 1)
//closes the door (bit 0)
//sends message to elevator
do
  :: openclosedoor?eval(i),1;
  doorisopen[i-1]=1;
  doorisopen[i-1]=0;
  openclosedoor!i,0;
od
}
//cabin goes up or down or stays or floor door opens and closes
proctype elevator()
{
do
   :: (floor!=3) ->
moveUp: floor++;
   :: (floor!=1) ->
moveDown: floor--;
   :: openclosedoor!floor,1;
      openclosedoor?eval(floor),0
od
}

init{
  atomic{
    run door(1);
    run door(2);
    run door(3);
    run elevator();
  }
}

ltl p1 { [](open1 -> <> close1) }
ltl p2 { [](
          (open1 -> floor1) &&
          (open2 -> floor2) &&
          (open3 -> floor3)
      )}
ltl p3 { [](moving -> close) }
//ltl p3 { [](open -> !moving) }

ltl p4 { <> open }

//ltl p5 { []<>(floor1)} TODO: Porque não?
ltl p5 { [](!floor1 -> <>floor1)}