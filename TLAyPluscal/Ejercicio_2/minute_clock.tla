-------------------- MODULE minute_clock --------------------
EXTENDS Naturals

(* DEFINICIÓN DE VARIABLES
 hr = horas
 min = minutos
 ind = indicador AM/PM
 *)

VARIABLES hr, min, ind

vars == << hr, min, ind >>

\* DEFINICIÓN DE RANGOS DE LAS VARIABLES

HR_RANGE == 1..12
MIN_RANGE == 0..59
IND_RANGE == {"AM", "PM"}

\* INICIALIZACIÓN EN CUALQUIER hr, min e ind

Init ==
    /\ hr \in HR_RANGE
    /\ min \in MIN_RANGE
    /\ ind \in IND_RANGE

\* DEFINICIÓN DE ACCIONES

Clock == 
    \/ /\ min < 59
       /\ min' = min + 1
       /\ UNCHANGED << hr, ind >>
    \/ /\ min = 59
       /\ min' = 0
       /\ IF hr = 11 THEN
             /\ hr' = hr + 1
             /\ ind' = IF ind = "AM" THEN "PM" ELSE "AM"
          ELSE IF hr = 12 THEN
             /\ hr' = 1
             /\ UNCHANGED ind
          ELSE
             /\ hr' = hr + 1
             /\ UNCHANGED ind

Next == Clock

\* DEFINICIÓN DE LA ESPECIFICACIÓN

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Clock)


\* DEFINICIÓN DE PROPOEDADES

(* Propiedades de tipo SAFETY, comprueba que los valores
de hr, min e ind siempre están dentro del rango establecido *)

TypeOK ==
    /\ hr \in 1..12
    /\ min \in 0..59
    /\ ind \in {"AM", "PM"}

(* Propiedades de tipo LIVENESS, comprueba que los cambios
sean cíclicos *)

AlwaysCycle == []
    \/ <> (hr = 12) ~> (hr = 1)
    \/ <> (min = 59) ~> (min = 0)
    \/ <> (ind = "AM") ~> (ind = "PM")
    \/ <> (ind = "PM") ~> (ind = "AM")

(* Propiedades de tipo ACCIÓN, comprueban que nunca vaya el
el reloj para atrás y que el cambio del indicador se efectua
correctamente *)

AlwaysUp ==
    [] [ \/ /\ min < 59 /\ min' = min + 1 /\ hr' = hr
          \/ /\ min = 59 /\ min' = 0
             /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1
       ]_<<hr,min>>


IndicatorOK == 
    []
        [/\ (min = 59 /\ hr = 11 /\ ind = "AM") => (ind' = "PM")
        /\ (min = 59 /\ hr = 11 /\ ind = "PM") => (ind' = "AM")
        ]_<<hr,ind,min>>



=========================================================
