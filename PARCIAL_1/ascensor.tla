---- MODULE ascensor ----
EXTENDS Naturals, FiniteSets

CONSTANTS PISOS \* Ejemplo: {1, 2, 3, 4}

(* --algorithm ascensor {

variables
    piso = 1,              \* Empezamos en el 1 (o elige uno de PISOS)
    requests = {},         \* Conjunto vacio
    door = "CLOSE",        \* "OPEN" o "CLOSE"
    direction = "STOP";    \* "UP", "DOWN", "STOP"

\* --- PROCESO USUARIO: Solo añade peticiones ---
fair process (AddPiso = "AddPiso")
{AddPiso:
    while(TRUE){
        with(p \in PISOS){
            requests := requests \union {p};
        };
    }
}

\* --- PROCESO ASCENSOR: El cerebro ---
fair process (Elevator = "Elevator")
{Elevator:
    while(TRUE){
        
        \* 1. COMPROBAR SI HEMOS LLEGADO
        if (piso \in requests) {
            requests := requests \ {piso}; \* Recuerda: restar conjuntos con { }
        };

        \* 2. DECIDIR DIRECCION (Corregido 'else if')
        if (direction = "STOP") {
            if (\E p \in requests : p > piso) { 
                direction := "UP"; 
            }
            else if (\E p \in requests : p < piso) {  \* <--- AQUI EL CAMBIO
                direction := "DOWN"; 
            }
        }
        else if (direction = "UP") {                  \* <--- AQUI EL CAMBIO
            if (\A p \in requests : p <= piso) {
                if (\E p \in requests : p < piso) { 
                    direction := "DOWN"; 
                }
                else { 
                    direction := "STOP"; 
                }
            }
        }
        else if (direction = "DOWN") {                \* <--- AQUI EL CAMBIO
            if (\A p \in requests : p >= piso) {
                if (\E p \in requests : p > piso) { 
                    direction := "UP"; 
                }
                else { 
                    direction := "STOP"; 
                }
            }
        };

        \* 3. MOVER EL ASCENSOR
        if (door = "CLOSE" /\ direction /= "STOP") {
            if (direction = "UP" /\ piso < 4) { 
                piso := piso + 1;
            }
            else if (direction = "DOWN" /\ piso > 1) { \* <--- AQUI EL CAMBIO
                 piso := piso - 1;
            }
        }
    }
}

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "776ebe8a" /\ chksum(tla) = "7aa5367f")
\* Label AddPiso of process AddPiso at line 17 col 5 changed to AddPiso_
\* Label Elevator of process Elevator at line 27 col 5 changed to Elevator_
VARIABLES piso, requests, door, direction

vars == << piso, requests, door, direction >>

ProcSet == {"AddPiso"} \cup {"Elevator"}

Init == (* Global variables *)
        /\ piso = 1
        /\ requests = {}
        /\ door = "CLOSE"
        /\ direction = "STOP"

AddPiso == /\ \E p \in PISOS:
                requests' = (requests \union {p})
           /\ UNCHANGED << piso, door, direction >>

Elevator == /\ IF piso \in requests
                  THEN /\ requests' = requests \ {piso}
                  ELSE /\ TRUE
                       /\ UNCHANGED requests
            /\ IF direction = "STOP"
                  THEN /\ IF \E p \in requests' : p > piso
                             THEN /\ direction' = "UP"
                             ELSE /\ IF \E p \in requests' : p < piso
                                        THEN /\ direction' = "DOWN"
                                        ELSE /\ TRUE
                                             /\ UNCHANGED direction
                  ELSE /\ IF direction = "UP"
                             THEN /\ IF \A p \in requests' : p <= piso
                                        THEN /\ IF \E p \in requests' : p < piso
                                                   THEN /\ direction' = "DOWN"
                                                   ELSE /\ direction' = "STOP"
                                        ELSE /\ TRUE
                                             /\ UNCHANGED direction
                             ELSE /\ IF direction = "DOWN"
                                        THEN /\ IF \A p \in requests' : p >= piso
                                                   THEN /\ IF \E p \in requests' : p > piso
                                                              THEN /\ direction' = "UP"
                                                              ELSE /\ direction' = "STOP"
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED direction
                                        ELSE /\ TRUE
                                             /\ UNCHANGED direction
            /\ IF door = "CLOSE" /\ direction' /= "STOP"
                  THEN /\ IF direction' = "UP" /\ piso < 4
                             THEN /\ piso' = piso + 1
                             ELSE /\ IF direction' = "DOWN" /\ piso > 1
                                        THEN /\ piso' = piso - 1
                                        ELSE /\ TRUE
                                             /\ piso' = piso
                  ELSE /\ TRUE
                       /\ piso' = piso
            /\ door' = door

Next == AddPiso \/ Elevator

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(AddPiso)
        /\ WF_vars(Elevator)

\* END TRANSLATION 

====
