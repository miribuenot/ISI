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
    /\ UNCHANGED display

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
    /\ UNCHANGED sensor

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

(* ---------------- NEXT + SPEC ---------------- *)
Next == 
    /\ (ReadSensor \/ UpdateDisplay)
    /\ Clock

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

(* LIVENESS: siempre hay ciclos *)
AlwaysCycle ==
    [] ( \/ (hr = 12) ~> (hr = 1)
         \/ (min = 59) ~> (min = 0)
         \/ (ind = "AM") ~> (ind = "PM")
         \/ (ind = "PM") ~> (ind = "AM")
       )

(* ACCIÓN: nunca retrocede *)
AlwaysUp ==
    [] [ \/ /\ min < 59
            /\ min' = min + 1
            /\ hr' = hr
         \/ /\ min = 59
            /\ min' = 0
            /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1
       ]_<<hr, min>>

(* El indicador cambia en el momento correcto *)
IndicatorOK ==
    [] [ /\ (min = 59 /\ hr = 11 /\ ind = "AM") => (ind' = "PM")
         /\ (min = 59 /\ hr = 11 /\ ind = "PM") => (ind' = "AM")
       ]_<<hr, ind, min>>

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
