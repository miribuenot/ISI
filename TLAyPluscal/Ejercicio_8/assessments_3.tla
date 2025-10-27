---- MODULE assessments_3 ----
Professors == {"prof_1", "prof_2"} 
Students   == {"student_1", "student_2", "student_3"} 

(*--algorithm Assessments {
variables
	graded_students = [p \in Professors |-> {}],
    locked = {};


define {
	NoDoubleGrading == \A p1, p2 \in Professors:
	  graded_students[p1] \cap graded_students[p2] /= {} => p1 = p2
    AllStudentsGraded == <>(\A s \in Students: \E p \in Professors: (s \in graded_students[p]))
    AllStudentsGradedbyProf == \A p \in Professors : pc[p] = "Done" => (Students \ locked = {})

}

process (Professor \in Professors) 
	variable selected = {};
{	
    SelectStudents:
    with (s \in SUBSET (Students \ locked)) {
        selected := s
    };        
    locked := locked \cup selected;

    ExamDay:
    either {
        (* Exam done! *)
        graded_students[self] := selected
    }
    or  {
        (* Professor can't finally do the exam *)
        skip;
        (* unlock students *)
        locked := locked \ selected;
    }
}

process (Cleanup = "cleanup")
{   Finally:
    when \A p \in Professors: pc[p] = "Done";
    with (p \in Professors) { 
        graded_students[p] := graded_students[p] \cup (Students \ locked)
    }
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d9acd7ac" /\ chksum(tla) = "3739d050")
VARIABLES pc, graded_students, locked

(* define statement *)
    NoDoubleGrading == \A p1, p2 \in Professors:
      graded_students[p1] \cap graded_students[p2] /= {} => p1 = p2
AllStudentsGraded == <>(\A s \in Students: \E p \in Professors: (s \in graded_students[p]))
AllStudentsGradedbyProf == \A p \in Professors : pc[p] = "Done" => (Students \ locked = {})

VARIABLE selected

vars == << pc, graded_students, locked, selected >>

ProcSet == (Professors) \cup {"cleanup"}

Init == (* Global variables *)
        /\ graded_students = [p \in Professors |-> {}]
        /\ locked = {}
        (* Process Professor *)
        /\ selected = [self \in Professors |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in Professors -> "SelectStudents"
                                        [] self = "cleanup" -> "Finally"]

SelectStudents(self) == /\ pc[self] = "SelectStudents"
                        /\ \E s \in SUBSET (Students \ locked):
                             selected' = [selected EXCEPT ![self] = s]
                        /\ locked' = (locked \cup selected'[self])
                        /\ pc' = [pc EXCEPT ![self] = "ExamDay"]
                        /\ UNCHANGED graded_students

ExamDay(self) == /\ pc[self] = "ExamDay"
                 /\ \/ /\ graded_students' = [graded_students EXCEPT ![self] = selected[self]]
                       /\ UNCHANGED locked
                    \/ /\ TRUE
                       /\ locked' = locked \ selected[self]
                       /\ UNCHANGED graded_students
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED selected

Professor(self) == SelectStudents(self) \/ ExamDay(self)

Finally == /\ pc["cleanup"] = "Finally"
           /\ \A p \in Professors: pc[p] = "Done"
           /\ \E p \in Professors:
                graded_students' = [graded_students EXCEPT ![p] = graded_students[p] \cup (Students \ locked)]
           /\ pc' = [pc EXCEPT !["cleanup"] = "Done"]
           /\ UNCHANGED << locked, selected >>

Cleanup == Finally

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Cleanup
           \/ (\E self \in Professors: Professor(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
