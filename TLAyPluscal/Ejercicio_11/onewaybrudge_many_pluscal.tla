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

(*--algorithm OneWayBridgeLights {
variables 
    lights    = [island \in ISLANDS |-> "red"];  
    sensors   = [island \in ISLANDS |-> {}], 
    bridgeCam = <<>>, 
    cars      = [island \in ISLANDS |-> IF island = "left" THEN INITIAL_CARS_L 
                                      ELSE INITIAL_CARS_R],
    MAX_CARS  = [island \in ISLANDS |-> IF island = "left" THEN MAX_CARS_L 
                                      ELSE MAX_CARS_R], 
    last_platoon_length = 0

(********************************************************************************)
(*                                                                              *)
(*                                                                              *)
(*                                                                              *)
(*                             ESCRIBE AQUÍ TU CÓDIGO                           *)
(*                                                                              *)
(*                                                                              *)
(*                                                                              *)
(********************************************************************************)

*)
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
