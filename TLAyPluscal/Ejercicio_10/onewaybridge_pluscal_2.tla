---- MODULE onewaybridge_pluscal_2 ----
EXTENDS FiniteSets, Integers

CONSTANT 
    MAX_CARS_L,       \* max number of cars in left  island
    MAX_CARS_R,       \* max number of cars in right island
    INITIAL_CARS_L,   \* set of cars initially in left  island
    INITIAL_CARS_R,   \* set of cars initially in right island
    ISLANDS           \* set of names of islands

ASSUME \A car \in INITIAL_CARS_R \cup INITIAL_CARS_L: car \in STRING
ASSUME MAX_CARS_L >= Cardinality(INITIAL_CARS_L) 
ASSUME MAX_CARS_R >= Cardinality(INITIAL_CARS_R)

(*--algorithm OneWayBridgeLights {
variables 
    lights    = [island \in ISLANDS |-> "red"];  
    sensors   = [island \in ISLANDS |-> {}], 
    bridgeCam = {}, 
    cars      = [island \in ISLANDS |-> IF island = "left" THEN INITIAL_CARS_L 
                                      ELSE INITIAL_CARS_R],
    MAX_CARS  = [island \in ISLANDS |-> IF island = "left" THEN MAX_CARS_L 
                                      ELSE MAX_CARS_R], 

fair process (AccessToBridge = "accesstobridge")
    variable otherIsland = "";
{   AccessToBridge:
    while (TRUE) {
        with (anIsland \in ISLANDS) {
            either{ \* car moves into sensor
                when (sensors[anIsland] = {}); 
                with (car \in cars[anIsland]) {
                    sensors[anIsland] := sensors[anIsland] \union {car};
                }
            }
            or{ \* switch light into green 
                otherIsland := IF anIsland = "left" THEN "right" ELSE "left";
                when ( /\ sensors[anIsland] /= {}
                       /\ Cardinality(cars[otherIsland]) < MAX_CARS[otherIsland]
                       /\ bridgeCam = {}
                       /\ lights[anIsland]     = "red"
                       /\ lights[otherIsland]  = "red"
                );

                lights[anIsland] := "green";            
            }
        }
    } 
}

process (EnterBridge = "enterbridge")
    variable otherIsland = "", leavingIsland = "";
{   EnterBridge:
    while (TRUE) {
        with (anIsland \in ISLANDS) {
            when ( /\ sensors[anIsland] /= {}
                   /\ lights [anIsland] =  "green" );                
            with (car \in sensors[anIsland]) {
                sensors[anIsland] := {};
                cars[anIsland] := cars[anIsland] \ {car}; 

                otherIsland := IF leavingIsland = "left" THEN "right" ELSE "left";
                bridgeCam := bridgeCam \cup {<<car, otherIsland>>};

                leavingIsland := anIsland;
            };
        };
        LightsToRed:
        if (leavingIsland /= "") lights[leavingIsland] := "red"; 
    }    
}

fair process (ExitBridge ="exitbridge") 
{   ExitBridge:
    while (TRUE) {
        when (bridgeCam /= {});
        with (carInBridge \in bridgeCam) { 
            bridgeCam := {};
            cars[carInBridge[2]] := cars[carInBridge[2]] \cup {carInBridge[1]}; 
        }
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a9c7a6e5" /\ chksum(tla) = "800c7d7")
\* Label AccessToBridge of process AccessToBridge at line 28 col 5 changed to AccessToBridge_
\* Label EnterBridge of process EnterBridge at line 54 col 5 changed to EnterBridge_
\* Label ExitBridge of process ExitBridge at line 75 col 5 changed to ExitBridge_
\* Process variable otherIsland of process AccessToBridge at line 26 col 14 changed to otherIsland_
VARIABLES pc, lights, sensors, bridgeCam, cars, MAX_CARS, otherIsland_, 
          otherIsland, leavingIsland

vars == << pc, lights, sensors, bridgeCam, cars, MAX_CARS, otherIsland_, 
           otherIsland, leavingIsland >>

ProcSet == {"accesstobridge"} \cup {"enterbridge"} \cup {"exitbridge"}

Init == (* Global variables *)
        /\ lights = [island \in ISLANDS |-> "red"]
        /\ sensors = [island \in ISLANDS |-> {}]
        /\ bridgeCam = {}
        /\ cars = [island \in ISLANDS |-> IF island = "left" THEN INITIAL_CARS_L
                                        ELSE INITIAL_CARS_R]
        /\ MAX_CARS = [island \in ISLANDS |-> IF island = "left" THEN MAX_CARS_L
                                            ELSE MAX_CARS_R]
        (* Process AccessToBridge *)
        /\ otherIsland_ = ""
        (* Process EnterBridge *)
        /\ otherIsland = ""
        /\ leavingIsland = ""
        /\ pc = [self \in ProcSet |-> CASE self = "accesstobridge" -> "AccessToBridge_"
                                        [] self = "enterbridge" -> "EnterBridge_"
                                        [] self = "exitbridge" -> "ExitBridge_"]

AccessToBridge_ == /\ pc["accesstobridge"] = "AccessToBridge_"
                   /\ \E anIsland \in ISLANDS:
                        \/ /\ (sensors[anIsland] = {})
                           /\ \E car \in cars[anIsland]:
                                sensors' = [sensors EXCEPT ![anIsland] = sensors[anIsland] \union {car}]
                           /\ UNCHANGED <<lights, otherIsland_>>
                        \/ /\ otherIsland_' = (IF anIsland = "left" THEN "right" ELSE "left")
                           /\      ( /\ sensors[anIsland] /= {}
                                     /\ Cardinality(cars[otherIsland_']) < MAX_CARS[otherIsland_']
                                     /\ bridgeCam = {}
                                     /\ lights[anIsland]     = "red"
                                     /\ lights[otherIsland_']  = "red"
                              )
                           /\ lights' = [lights EXCEPT ![anIsland] = "green"]
                           /\ UNCHANGED sensors
                   /\ pc' = [pc EXCEPT !["accesstobridge"] = "AccessToBridge_"]
                   /\ UNCHANGED << bridgeCam, cars, MAX_CARS, otherIsland, 
                                   leavingIsland >>

AccessToBridge == AccessToBridge_

EnterBridge_ == /\ pc["enterbridge"] = "EnterBridge_"
                /\ \E anIsland \in ISLANDS:
                     /\ ( /\ sensors[anIsland] /= {}
                          /\ lights [anIsland] =  "green" )
                     /\ \E car \in sensors[anIsland]:
                          /\ sensors' = [sensors EXCEPT ![anIsland] = {}]
                          /\ cars' = [cars EXCEPT ![anIsland] = cars[anIsland] \ {car}]
                          /\ otherIsland' = (IF leavingIsland = "left" THEN "right" ELSE "left")
                          /\ bridgeCam' = (bridgeCam \cup {<<car, otherIsland'>>})
                          /\ leavingIsland' = anIsland
                /\ pc' = [pc EXCEPT !["enterbridge"] = "LightsToRed"]
                /\ UNCHANGED << lights, MAX_CARS, otherIsland_ >>

LightsToRed == /\ pc["enterbridge"] = "LightsToRed"
               /\ IF leavingIsland /= ""
                     THEN /\ lights' = [lights EXCEPT ![leavingIsland] = "red"]
                     ELSE /\ TRUE
                          /\ UNCHANGED lights
               /\ pc' = [pc EXCEPT !["enterbridge"] = "EnterBridge_"]
               /\ UNCHANGED << sensors, bridgeCam, cars, MAX_CARS, 
                               otherIsland_, otherIsland, leavingIsland >>

EnterBridge == EnterBridge_ \/ LightsToRed

ExitBridge_ == /\ pc["exitbridge"] = "ExitBridge_"
               /\ (bridgeCam /= {})
               /\ \E carInBridge \in bridgeCam:
                    /\ bridgeCam' = {}
                    /\ cars' = [cars EXCEPT ![carInBridge[2]] = cars[carInBridge[2]] \cup {carInBridge[1]}]
               /\ pc' = [pc EXCEPT !["exitbridge"] = "ExitBridge_"]
               /\ UNCHANGED << lights, sensors, MAX_CARS, otherIsland_, 
                               otherIsland, leavingIsland >>

ExitBridge == ExitBridge_

Next == AccessToBridge \/ EnterBridge \/ ExitBridge

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(AccessToBridge)
        /\ WF_vars(ExitBridge)

\* END TRANSLATION 

\* Invriants
MaxCapInv ==
    \A isl \in ISLANDS : Cardinality(cars[isl]) <= MAX_CARS[isl]

SemaforoInv ==
    \A isl \in ISLANDS : lights[isl] \in {"red", "green"}

CamaraInv ==
    Cardinality(bridgeCam) <= 1

No2Verde ==
    ~(\E left \in ISLANDS :
         LET right == IF left = "left" THEN "right" ELSE "left" IN
           lights[left] = "green" /\ lights[right] = "green")

SensorRojoInv ==
    \A isl \in ISLANDS : sensors[isl] = {} => lights[isl] = "red"

ControlCapInv ==
    \A isl \in ISLANDS :
      Cardinality(cars[isl]) = MAX_CARS[isl] =>
        LET other == IF isl = "left" THEN "right" ELSE "left" IN
           lights[other] = "red"

\*Liveness

TurnVerde ==
    [](
        \A isl \in ISLANDS :
           lights[isl] = "green" =>
             /\ sensors[isl] /= {}
             /\ LET other == IF isl = "left" THEN "right" ELSE "left" IN
                  Cardinality(cars[other]) < MAX_CARS[other]
             /\ bridgeCam = {}
    )

AntesVerde ==
    \A isl \in ISLANDS :
      ( sensors[isl] /= {} /\ LET other == IF isl = "left" THEN "right" ELSE "left" IN
                           Cardinality(cars[other]) < MAX_CARS[other] /\ bridgeCam = {} )
       ~> ( lights[isl] = "green" )

\*Accion

TurnRojo ==
    []( 
        \A isl \in ISLANDS :
            (lights[isl] = "green" /\ bridgeCam # {}) 
              => lights[isl] = "red"
    )
====
