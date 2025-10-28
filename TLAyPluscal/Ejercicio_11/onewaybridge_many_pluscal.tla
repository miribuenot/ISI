---- MODULE onewaybridge_many_pluscal ----
EXTENDS Sequences, FiniteSets, Integers

CONSTANT 
    MAX_CARS_L,         \* max number of cars in left  island
    MAX_CARS_R,         \* max number of cars in right island
    INITIAL_CARS_L,     \* set of cars initially in left  island
    INITIAL_CARS_R,     \* set of cars initially in right island
    ISLANDS,            \* set of names of islands
    MAX_CARS_IN_BRIDGE, \* max number of cars in bridge
    MAX_PLATOON         \* if car waiting at sensor it can not see
                        \* more than MAX_PLATOON cars coming from the other island

ASSUME \A car \in INITIAL_CARS_R \cup INITIAL_CARS_L: car \in STRING
ASSUME MAX_CARS_L >= Cardinality(INITIAL_CARS_L) 
ASSUME MAX_CARS_R >= Cardinality(INITIAL_CARS_R)
ASSUME MAX_PLATOON >= MAX_CARS_IN_BRIDGE

\* Helper operator: Counts cars on the bridge going to 'island'
CarsOnBridgeTo(bCam, island) ==
  Len(SelectSeq(bCam, LAMBDA c: c[2] = island))

(*--algorithm OneWayBridgeLights {
variables 
    lights    = [island \in ISLANDS |-> "red"];  
    sensors   = [island \in ISLANDS |-> {}], 
    bridgeCam = <<>>, 
    cars      = [island \in ISLANDS |-> IF island = "left" THEN INITIAL_CARS_L 
                                      ELSE INITIAL_CARS_R],
    MAX_CARS  = [island \in ISLANDS |-> IF island = "left" THEN MAX_CARS_L 
                                      ELSE MAX_CARS_R], 
    last_platoon_length = 0,
    start = 0

fair process (AccessToBridge = "accesstobridge")
{   AccessToBridge:
    while (TRUE) {
        with (anIsland \in ISLANDS) {

            either {  \* Car moves into sensor
                when (sensors[anIsland] = {}); 
                with (car \in cars[anIsland]) {
                    sensors[anIsland] := sensors[anIsland] \union {car};

                    with (otherIsland \in {"left", "right"}) {
                        when (otherIsland # anIsland);

                        either {
                            when (
                                /\ sensors[otherIsland] = {}
                                /\ lights[otherIsland] = "green"
                            );
                            lights[otherIsland] := "red";
                        }
                        or {
                            when (
                                /\ sensors[otherIsland] /= {}
                                /\ lights[otherIsland] = "green"
                            );
                            last_platoon_length := Len(bridgeCam);
                            start := 1;
                        }
                        or {
                            when (lights[otherIsland] = "red");
                            skip;
                        }
                    }
                }
            }

            or {  \* Switch light into green
                with (otherIsland \in {"left", "right"}) {
                    when (otherIsland # anIsland
                          /\ sensors[anIsland] /= {}
                          /\ Cardinality(cars[otherIsland]) < MAX_CARS[otherIsland]
                          /\ bridgeCam = <<>>
                          /\ lights[anIsland] = "red"
                          /\ lights[otherIsland] = "red"
                    );

                    lights[anIsland] := "green";  
                    last_platoon_length := 0;
                    start := 0;  
                }
            }

        }
    }
}

fair process (EnterBridge = "enterbridge")
{   EnterBridge:
    while (TRUE) {
        with (anIsland \in ISLANDS) {
            
            when ( /\ sensors[anIsland] /= {}
                   /\ lights [anIsland] =  "green"
                   /\ Len(bridgeCam) < MAX_CARS_IN_BRIDGE
                   /\ (IF Len(bridgeCam) = 0 THEN TRUE ELSE bridgeCam[1][2] # anIsland)
                   /\ last_platoon_length < MAX_PLATOON
                   /\ (IF anIsland = "left"
                       THEN Cardinality(cars["right"]) + CarsOnBridgeTo(bridgeCam, "right") < MAX_CARS["right"]
                       ELSE Cardinality(cars["left"]) + CarsOnBridgeTo(bridgeCam, "left") < MAX_CARS["left"])
                 ); 
                 
            with (car \in sensors[anIsland]) {
                sensors[anIsland] := {};
                cars[anIsland] := cars[anIsland] \ {car}; 

                bridgeCam := 
                    LET otherIsland == IF anIsland = "left" THEN "right" ELSE "left"
                    IN 
                        Append(bridgeCam, <<car, otherIsland>>)
                ; 

                if (start = 1) {
                    last_platoon_length := last_platoon_length + 1;
                };

                
                if (Len(bridgeCam) = MAX_CARS_IN_BRIDGE) {
                    lights[anIsland] := "red";
                }
            }
        }
    }
}
fair process (ExitBridge ="exitbridge") 
{   ExitBridge:
    while (TRUE) {
        when (bridgeCam /= <<>>);
        
        with (carInBridge = Head(bridgeCam)) {
             bridgeCam := Tail(bridgeCam);
             cars[carInBridge[2]] := cars[carInBridge[2]] \cup {carInBridge[1]};

             if (Cardinality(cars[carInBridge[2]]) = MAX_CARS[carInBridge[2]]) {

                 if (carInBridge[2] = "left") {
                     lights["right"] := "red";
                 } else {
                     lights["left"] := "red";
                 }
             }
        }
    }
}

fair process (StopPlatoon = "stopplatoon")
{   StopPlatoon:
    while (TRUE) {
        with (anIsland \in ISLANDS) {
            
            when (
                 LET otherIsland == IF anIsland = "left" THEN "right" ELSE "left"
                 IN
                    /\ lights[anIsland] = "green"      
                    /\ sensors[otherIsland] /= {}      
                    /\ last_platoon_length >= MAX_PLATOON 
             ); 
            
            lights[anIsland] := "red"
        }
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "81faa524" /\ chksum(tla) = "89f2a24b")
\* Label AccessToBridge of process AccessToBridge at line 37 col 5 changed to AccessToBridge_
\* Label EnterBridge of process EnterBridge at line 93 col 5 changed to EnterBridge_
\* Label ExitBridge of process ExitBridge at line 134 col 5 changed to ExitBridge_
\* Label StopPlatoon of process StopPlatoon at line 156 col 5 changed to StopPlatoon_
VARIABLES lights, sensors, bridgeCam, cars, MAX_CARS, last_platoon_length, 
          start

vars == << lights, sensors, bridgeCam, cars, MAX_CARS, last_platoon_length, 
           start >>

ProcSet == {"accesstobridge"} \cup {"enterbridge"} \cup {"exitbridge"} \cup {"stopplatoon"}

Init == (* Global variables *)
        /\ lights = [island \in ISLANDS |-> "red"]
        /\ sensors = [island \in ISLANDS |-> {}]
        /\ bridgeCam = <<>>
        /\ cars = [island \in ISLANDS |-> IF island = "left" THEN INITIAL_CARS_L
                                        ELSE INITIAL_CARS_R]
        /\ MAX_CARS = [island \in ISLANDS |-> IF island = "left" THEN MAX_CARS_L
                                            ELSE MAX_CARS_R]
        /\ last_platoon_length = 0
        /\ start = 0

AccessToBridge == /\ \E anIsland \in ISLANDS:
                       \/ /\ (sensors[anIsland] = {})
                          /\ \E car \in cars[anIsland]:
                               /\ sensors' = [sensors EXCEPT ![anIsland] = sensors[anIsland] \union {car}]
                               /\ \E otherIsland \in {"left", "right"}:
                                    /\ (otherIsland # anIsland)
                                    /\ \/ /\      (
                                                 /\ sensors'[otherIsland] = {}
                                                 /\ lights[otherIsland] = "green"
                                             )
                                          /\ lights' = [lights EXCEPT ![otherIsland] = "red"]
                                          /\ UNCHANGED <<last_platoon_length, start>>
                                       \/ /\      (
                                                 /\ sensors'[otherIsland] /= {}
                                                 /\ lights[otherIsland] = "green"
                                             )
                                          /\ last_platoon_length' = Len(bridgeCam)
                                          /\ start' = 1
                                          /\ UNCHANGED lights
                                       \/ /\ (lights[otherIsland] = "red")
                                          /\ TRUE
                                          /\ UNCHANGED <<lights, last_platoon_length, start>>
                       \/ /\ \E otherIsland \in {"left", "right"}:
                               /\      (otherIsland # anIsland
                                        /\ sensors[anIsland] /= {}
                                        /\ Cardinality(cars[otherIsland]) < MAX_CARS[otherIsland]
                                        /\ bridgeCam = <<>>
                                        /\ lights[anIsland] = "red"
                                        /\ lights[otherIsland] = "red"
                                  )
                               /\ lights' = [lights EXCEPT ![anIsland] = "green"]
                               /\ last_platoon_length' = 0
                               /\ start' = 0
                          /\ UNCHANGED sensors
                  /\ UNCHANGED << bridgeCam, cars, MAX_CARS >>

EnterBridge == /\ \E anIsland \in ISLANDS:
                    /\ ( /\ sensors[anIsland] /= {}
                         /\ lights [anIsland] =  "green"
                         /\ Len(bridgeCam) < MAX_CARS_IN_BRIDGE
                         /\ (IF Len(bridgeCam) = 0 THEN TRUE ELSE bridgeCam[1][2] # anIsland)
                         /\ last_platoon_length < MAX_PLATOON
                       
                       
                       
                         /\ (IF anIsland = "left"
                             THEN Cardinality(cars["right"]) + CarsOnBridgeTo(bridgeCam, "right") < MAX_CARS["right"]
                             ELSE Cardinality(cars["left"]) + CarsOnBridgeTo(bridgeCam, "left") < MAX_CARS["left"])
                       )
                    /\ \E car \in sensors[anIsland]:
                         /\ sensors' = [sensors EXCEPT ![anIsland] = {}]
                         /\ cars' = [cars EXCEPT ![anIsland] = cars[anIsland] \ {car}]
                         /\ bridgeCam' = (LET otherIsland == IF anIsland = "left" THEN "right" ELSE "left"
                                          IN
                                              Append(bridgeCam, <<car, otherIsland>>))
                         /\ IF start = 1
                               THEN /\ last_platoon_length' = last_platoon_length + 1
                               ELSE /\ TRUE
                                    /\ UNCHANGED last_platoon_length
                         /\ IF Len(bridgeCam') = MAX_CARS_IN_BRIDGE
                               THEN /\ lights' = [lights EXCEPT ![anIsland] = "red"]
                               ELSE /\ TRUE
                                    /\ UNCHANGED lights
               /\ UNCHANGED << MAX_CARS, start >>

ExitBridge == /\ (bridgeCam /= <<>>)
              /\ LET carInBridge == Head(bridgeCam) IN
                   /\ bridgeCam' = Tail(bridgeCam)
                   /\ cars' = [cars EXCEPT ![carInBridge[2]] = cars[carInBridge[2]] \cup {carInBridge[1]}]
                   /\ IF Cardinality(cars'[carInBridge[2]]) = MAX_CARS[carInBridge[2]]
                         THEN /\ IF carInBridge[2] = "left"
                                    THEN /\ lights' = [lights EXCEPT !["right"] = "red"]
                                    ELSE /\ lights' = [lights EXCEPT !["left"] = "red"]
                         ELSE /\ TRUE
                              /\ UNCHANGED lights
              /\ UNCHANGED << sensors, MAX_CARS, last_platoon_length, start >>

StopPlatoon == /\ \E anIsland \in ISLANDS:
                    /\     (
                       
                       
                           LET otherIsland == IF anIsland = "left" THEN "right" ELSE "left"
                           IN
                              /\ lights[anIsland] = "green"
                              /\ sensors[otherIsland] /= {}
                              /\ last_platoon_length >= MAX_PLATOON
                       )
                    /\ lights' = [lights EXCEPT ![anIsland] = "red"]
               /\ UNCHANGED << sensors, bridgeCam, cars, MAX_CARS, 
                               last_platoon_length, start >>

Next == AccessToBridge \/ EnterBridge \/ ExitBridge \/ StopPlatoon

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(AccessToBridge)
        /\ WF_vars(EnterBridge)
        /\ WF_vars(ExitBridge)
        /\ WF_vars(StopPlatoon)

\* END TRANSLATION 
----
(**********)
(* Safety *)
(**********)

MaxCarsInBridge == Len(bridgeCam) <= MAX_CARS_IN_BRIDGE

NoBothLightsGreen == 
    ~ (lights["right"] = "green" /\ lights["left"] = "green")

RespectMaxCars == /\ Cardinality(cars["right"]) <= MAX_CARS["right"]
                  /\ Cardinality(cars["left"])  <= MAX_CARS["left"]

NoCarsLost == Cardinality(INITIAL_CARS_L) + Cardinality(INITIAL_CARS_R) = Len(bridgeCam) + Cardinality(cars["left"]) + Cardinality(cars["right"])

LightRedIfIslandFull ==
    /\ Cardinality(cars["right"]) = MAX_CARS["right"] => lights["left"]  = "red"
    /\ Cardinality(cars["left"])  = MAX_CARS["left"]  => lights["right"] = "red"


AllCarsInBridgeHaveSameDestination ==
    \A i \in 2..Len(bridgeCam): bridgeCam[i][2] = bridgeCam[1][2]

BigPlatoonsOnlyIfNoCarsWaiting == last_platoon_length > MAX_PLATOON => 
    \/ lights["left"]  = "green" /\ sensors["right"] = {}
    \/ lights["right"] = "green" /\ sensors["left"]  = {}
  
BothLightsRedIfBridgeFull ==   
    Len(bridgeCam) = MAX_CARS_IN_BRIDGE => \A island \in ISLANDS: lights[island] = "red"


(**********************)
(****** Liveness ******)
(**********************)

BridgeAlwaysEventuallyEmpty == 
    []<>(Len(bridgeCam) > 0 ~> Len(bridgeCam) = 0)

EventuallyLightGreenIfCarInSensor == 
    /\ [] (sensors["left"]  /= {} => <> (lights["left"]  = "green"))
    /\ [] (sensors["right"] /= {} => <> (lights["right"] = "green"))

CarsAtSensorEnterBridge == 
    \A car \in INITIAL_CARS_L \cup INITIAL_CARS_R: 
        /\ sensors["left"]  = {car} => 
            <> (sensors["left"]  = {} ~> \E i \in 1..Len(bridgeCam): bridgeCam[i] = <<car, "right">> )
        /\ sensors["right"] = {car} => 
            <> (sensors["right"] = {} ~> \E i \in 1..Len(bridgeCam): bridgeCam[i] = <<car, "left">> )

(*******************************)
(****** Action Properties ******)
(*******************************)

LightStaysGreenIfNoCarWantsToCome ==
    [][ \A anIsland \in ISLANDS:
          LET other == IF anIsland = "left" THEN "right" ELSE "left"
          IN
            (   /\ lights[anIsland] = "green" 
                /\ sensors[other] = {}
                /\ Len(bridgeCam') + Cardinality(cars'[other]) < MAX_CARS[other]
                /\ Len(bridgeCam') < MAX_CARS_IN_BRIDGE
                /\ sensors'[other] = {}

            )
            =>  lights'[anIsland] = "green" 
    ]_vars    


LightRedIfPlatoonSentAndCarWantsToCome ==
    [][ \A anIsland \in ISLANDS:
          LET other == IF anIsland = "left" THEN "right" ELSE "left"
          IN     
            (   /\ lights[anIsland] = "green" 
                /\ last_platoon_length > MAX_PLATOON
                /\ sensors[anIsland] /= {}
                /\ sensors[other] /= {}
            )
            => lights'[anIsland] = "red"
    ]_vars    

LightStaysGreenIfCarsWantsToComeButWeHaveCarsToSendAndMaxPlatoonNotReachedYet ==
    [][ \A anIsland \in ISLANDS:
          LET other == IF anIsland = "left" THEN "right" ELSE "left"
          IN     
            (   /\ lights[anIsland] = "green" 
                /\ last_platoon_length < MAX_PLATOON
                /\ sensors[anIsland] /= {}
                /\ sensors[other] /= {}
                /\ Len(bridgeCam') + Cardinality(cars'[other]) < MAX_CARS [other] 
                /\ Len(bridgeCam') < MAX_CARS_IN_BRIDGE
            )
            =>  lights'[anIsland] = "green"
    ]_vars   
====
