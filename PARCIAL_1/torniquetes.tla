---- MODULE torniquetes ----
EXTENDS FiniteSets, Integers


CONSTANT 
    MAX_PERS_IN,
    TOR_IN,
    INITIAL_PERS_OUT,
    INITIAL_PERS_IN


(*--algorithm Torniquetes {
variables
    states_in = [tor \in TOR_IN |-> "open"],
    pers_in = INITIAL_PERS_IN,
    pers_out = INITIAL_PERS_OUT,
    n_open = Cardinality(TOR_IN);

fair process (EntrePerson = "entreperson")
{   EntrePerson:
    while(TRUE)
        with(torn \in TOR_IN) {
            either{
                when (states_in[torn] = "open");
                with(per \in pers_out) {
                    pers_in := pers_in \union {per};
                    pers_out := pers_out \ {per};
                
                    if ((Cardinality(pers_in) + n_open) > MAX_PERS_IN){
                        states_in[torn] := "close";
                        n_open := n_open - 1;
                    }
                }
            }
            or{
                when (
                /\ states_in[torn] = "close"
                /\ (Cardinality(pers_in) + n_open) < MAX_PERS_IN
                );

                states_in[torn] := "open";
                n_open := n_open + 1;

            }
        }
}

fair process (OutPerson = "outperson")
{   OutPerson:
    while(TRUE)
        with(per \in pers_in){
            pers_out := pers_out \union {per};
            pers_in := pers_in \ {per};
        }

}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2eb0c94e" /\ chksum(tla) = "e680c81b")
\* Label EntrePerson of process EntrePerson at line 21 col 5 changed to EntrePerson_
\* Label OutPerson of process OutPerson at line 50 col 5 changed to OutPerson_
VARIABLES states_in, pers_in, pers_out, n_open

vars == << states_in, pers_in, pers_out, n_open >>

ProcSet == {"entreperson"} \cup {"outperson"}

Init == (* Global variables *)
        /\ states_in = [tor \in TOR_IN |-> "open"]
        /\ pers_in = INITIAL_PERS_IN
        /\ pers_out = INITIAL_PERS_OUT
        /\ n_open = Cardinality(TOR_IN)

EntrePerson == \E torn \in TOR_IN:
                 \/ /\ (states_in[torn] = "open")
                    /\ \E per \in pers_out:
                         /\ pers_in' = (pers_in \union {per})
                         /\ pers_out' = pers_out \ {per}
                         /\ IF (Cardinality(pers_in') + n_open) > MAX_PERS_IN
                               THEN /\ states_in' = [states_in EXCEPT ![torn] = "close"]
                                    /\ n_open' = n_open - 1
                               ELSE /\ TRUE
                                    /\ UNCHANGED << states_in, n_open >>
                 \/ /\      (
                       /\ states_in[torn] = "close"
                       /\ (Cardinality(pers_in) + n_open) < MAX_PERS_IN
                       )
                    /\ states_in' = [states_in EXCEPT ![torn] = "open"]
                    /\ n_open' = n_open + 1
                    /\ UNCHANGED <<pers_in, pers_out>>

OutPerson == /\ \E per \in pers_in:
                  /\ pers_out' = (pers_out \union {per})
                  /\ pers_in' = pers_in \ {per}
             /\ UNCHANGED << states_in, n_open >>

Next == EntrePerson \/ OutPerson

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(EntrePerson)
        /\ WF_vars(OutPerson)

\* END TRANSLATION 

\* --- PROPIEDADES CORREGIDAS ---

AllPeople == INITIAL_PERS_IN \cup INITIAL_PERS_OUT

\* INVARIANTS
MaxCap == 
    Cardinality(pers_in) <= MAX_PERS_IN

MaxTorn ==
    Cardinality(pers_in) + n_open <= MAX_PERS_IN

NTorn ==
    n_open = Cardinality({t \in TOR_IN : states_in[t] = "open"})

\* PROPERTIES
\* Requisito 5 (Interpretación correcta para Conjuntos):
\* "Si el edificio está lleno, eventualmente se liberará espacio"
GoOut == 
    (Cardinality(pers_in) = MAX_PERS_IN) ~> (Cardinality(pers_in) < MAX_PERS_IN)

Entre ==
    (Cardinality(pers_in) < MAX_PERS_IN /\ pers_out # {}) 
    ~> (Cardinality(pers_in) > 0)
====
