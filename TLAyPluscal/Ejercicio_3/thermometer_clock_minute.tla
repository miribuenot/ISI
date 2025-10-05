----------------------------- MODULE thermometer_clock_minute -----------------------------
EXTENDS Naturals, Integers

(*
  VARIABLES:
  - display: valor mostrado en el termómetro
  - sensor : valor leído por el sensor
  - hr, min, ind : reloj (horas, minutos, indicador AM/PM)
*)

VARIABLES display, sensor, hr, min, ind

(* Agrupación de variables *)
varsth == << display, sensor >>
varscl == << hr, min, ind >>
vars   == << display, sensor, hr, min, ind >>

(* RANGOS *)
HR_RANGE == 1..12
MIN_RANGE == 0..59
IND_RANGE == {"AM", "PM"}

RANGE_TEMPS   == -1..1
MAX_INCREMENT == 2

(* ---------------- INIT ---------------- *)
Init ==
    /\ sensor  \in RANGE_TEMPS
    /\ display \in RANGE_TEMPS
    /\ hr \in HR_RANGE
    /\ min \in MIN_RANGE
    /\ ind \in IND_RANGE

(* ---------------- ACCIONES ---------------- *)

(* Leer del sensor *)
ReadSensor ==
    /\ IF display = sensor
          THEN sensor' \in RANGE_TEMPS
          ELSE sensor' = sensor
    /\ UNCHANGED <<display, hr, min, ind>>

(* Actualizar el display gradualmente *)
UpdateDisplay ==
    \/ /\ display > sensor
       /\ IF display - sensor > MAX_INCREMENT
             THEN display' = display - MAX_INCREMENT
             ELSE display' = sensor
    \/ /\ display < sensor
       /\ IF sensor - display > MAX_INCREMENT
             THEN display' = display + MAX_INCREMENT
             ELSE display' = sensor
    \/ /\ display = sensor
       /\ display' = display
    /\ UNCHANGED <<sensor, hr, min, ind>>

(* Reloj de 12 horas con AM/PM *)
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
    /\ UNCHANGED <<sensor, display>>

(* ---------------- NEXT + SPEC ---------------- *)
Next == 
    \/ ReadSensor
    \/ UpdateDisplay
    \/ Clock

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_sensor(ReadSensor)
    /\ WF_display(UpdateDisplay)
    /\ WF_varscl(Clock)

(* ---------------- PROPIEDADES ---------------- *)

(* SAFETY: rangos siempre respetados *)
TypeOK ==
    /\ sensor \in RANGE_TEMPS
    /\ display \in RANGE_TEMPS
    /\ hr \in HR_RANGE
    /\ min \in MIN_RANGE
    /\ ind \in IND_RANGE

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
    [] [
        \/ /\ min < 59
           /\ min' = min + 1 
           /\ hr' = hr
        \/ /\ min = 59 
           /\ min' = 0
           /\ \/ /\ hr = 12
                 /\ hr' = 1
                 /\ ind' = ind
              \/ /\ hr = 11
                 /\ hr' = 12
                 /\ \/ /\ ind = "AM"
                       /\ ind' = "PM"
                    \/ /\ ind = "PM"
                       /\ ind' = "AM"
              \/ /\ hr < 11
                 /\ hr' = hr + 1
                 /\ ind' = ind
       ]_<<hr,min,ind>>


IndicatorOK == 
    []
        [
            /\ (min = 59 /\ hr = 11 /\ ind = "AM") => (ind' = "PM")
            /\ (min = 59 /\ hr = 11 /\ ind = "PM") => (ind' = "AM")
        ]_<<hr,ind,min>>

(* Comprueban que en algún momento se tome cada valor del rango
tipo LIVENESS *)

AllHours == \A h \in HR_RANGE: <>(hr = h) 

AllMinutes == \A m \in MIN_RANGE: <>(min = m) 

AllInd == \A i \in IND_RANGE: <>(ind = i)

(* El display siempre alcanza al sensor *)
DisplayAlwaysReachesSensor ==
    [](display /= sensor => <> (display = sensor))

(* Incrementos siempre correctos *)
DisplayIncrementsOK ==
    [] [ IF display' < display THEN
            /\ display' >= sensor
            /\ display - display' <= MAX_INCREMENT
         ELSE IF display' > display THEN
            /\ display' <= sensor
            /\ display' - display <= MAX_INCREMENT
         ELSE display' = display
       ]_display

(* El sensor se mantiene salvo cuando display = sensor *)
ReadSensorOK ==
    [] [ IF display = sensor
         THEN sensor' \in RANGE_TEMPS
         ELSE sensor' = sensor
       ]_<<sensor, display>>

===================================================================================
