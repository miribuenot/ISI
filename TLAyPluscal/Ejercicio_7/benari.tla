---- MODULE benari ----
EXTENDS Integers, TLC

(* --algorithm benari { 
variables n = 0;

define {
    Threads == {"Thread_1", "Thread_2"}
    Reaches2AsInvariant == ( /\ pc["Thread_1"] = "Done" 
                              /\ pc["Thread_2"] = "Done") => n \in (2..20)
}

process (inc10 \in Threads) 
variables reg, count = 0;
{
    Benari:
    while (count < 10) {
        A1:
        reg   := n;
        
        A2:
        reg   := reg + 1;
        
        A3:
        n     := reg;

        A4:
        count := count + 1;
    };
    \* print <<self, n>>
}

process (Watcher = "Watcher"){
    Watcher: 
    when pc["Thread_1"] = "Done" /\ pc["Thread_2"] = "Done";
    print <<"Final value: ", n>>
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "bf0fd23b" /\ chksum(tla) = "8920d558")
\* Label Watcher of process Watcher at line 35 col 5 changed to Watcher_
CONSTANT defaultInitValue
VARIABLES pc, n

(* define statement *)
Threads == {"Thread_1", "Thread_2"}
Reaches2AsInvariant == ( /\ pc["Thread_1"] = "Done"
                          /\ pc["Thread_2"] = "Done") => n \in (2..20)

VARIABLES reg, count

vars == << pc, n, reg, count >>

ProcSet == (Threads) \cup {"Watcher"}

Init == (* Global variables *)
        /\ n = 0
        (* Process inc10 *)
        /\ reg = [self \in Threads |-> defaultInitValue]
        /\ count = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "Benari"
                                        [] self = "Watcher" -> "Watcher_"]

Benari(self) == /\ pc[self] = "Benari"
                /\ IF count[self] < 10
                      THEN /\ pc' = [pc EXCEPT ![self] = "A1"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << n, reg, count >>

A1(self) == /\ pc[self] = "A1"
            /\ reg' = [reg EXCEPT ![self] = n]
            /\ pc' = [pc EXCEPT ![self] = "A2"]
            /\ UNCHANGED << n, count >>

A2(self) == /\ pc[self] = "A2"
            /\ reg' = [reg EXCEPT ![self] = reg[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "A3"]
            /\ UNCHANGED << n, count >>

A3(self) == /\ pc[self] = "A3"
            /\ n' = reg[self]
            /\ pc' = [pc EXCEPT ![self] = "A4"]
            /\ UNCHANGED << reg, count >>

A4(self) == /\ pc[self] = "A4"
            /\ count' = [count EXCEPT ![self] = count[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "Benari"]
            /\ UNCHANGED << n, reg >>

inc10(self) == Benari(self) \/ A1(self) \/ A2(self) \/ A3(self) \/ A4(self)

Watcher_ == /\ pc["Watcher"] = "Watcher_"
            /\ pc["Thread_1"] = "Done" /\ pc["Thread_2"] = "Done"
            /\ PrintT(<<"Final value: ", n>>)
            /\ pc' = [pc EXCEPT !["Watcher"] = "Done"]
            /\ UNCHANGED << n, reg, count >>

Watcher == Watcher_

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Watcher
           \/ (\E self \in Threads: inc10(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
