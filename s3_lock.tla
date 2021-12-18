------------------------------ MODULE s3_lock ------------------------------
EXTENDS TLC, Integers
CONSTANT Threads
(*--algorithm s3lock

variables 
    MaxRounds = 20,
    rounds = [t \in Threads |-> 0];
  
fair process thread \in Threads
    variables round = 0;
begin

\* Acquire a lock over a shared resource.
LOCK:
    while TRUE do
L1:     if round > MaxRounds then
           goto FINISH;
        end if;
    
        \* Check if another thread has advanced beyond us, and if so, reset ourselves.
L2:     if \E t \in Threads \ {self}: rounds[t] > round then
            goto LOCK;
        end if;
        
        \* If we haven't played two rounds yet then we cannot possibly win yet, try
        \* to play another round.
L3:     if round < 2 then
            goto INCREMENT;
        end if;
    
        \* Check if we won the last two rounds and if so, enter the critical section.
 L4:    if \A t \in Threads \ {self}: rounds[t] <= (round - 2) then
            goto CS;
        end if;
        \* Try to win the next round.
 INCREMENT:
        round := round + 1;
 WRITE:
        rounds[self] := round;

    end while;
    
 \* Critical section. Only one process should make it here at a time.
CS:  skip;

\* Unlock a shared resource.
UNLOCK:
    rounds[self] := 0;

\* Extra label, only here to bound the model size.
FINISH: skip;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c2d955dd" /\ chksum(tla) = "b3685083")
VARIABLES MaxRounds, rounds, pc, round

vars == << MaxRounds, rounds, pc, round >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ MaxRounds = 20
        /\ rounds = [t \in Threads |-> 0]
        (* Process thread *)
        /\ round = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "LOCK"]

LOCK(self) == /\ pc[self] = "LOCK"
              /\ pc' = [pc EXCEPT ![self] = "L1"]
              /\ UNCHANGED << MaxRounds, rounds, round >>

L1(self) == /\ pc[self] = "L1"
            /\ IF round[self] > MaxRounds
                  THEN /\ pc' = [pc EXCEPT ![self] = "FINISH"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << MaxRounds, rounds, round >>

L2(self) == /\ pc[self] = "L2"
            /\ IF \E t \in Threads \ {self}: rounds[t] > round[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "LOCK"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L3"]
            /\ UNCHANGED << MaxRounds, rounds, round >>

L3(self) == /\ pc[self] = "L3"
            /\ IF round[self] < 2
                  THEN /\ pc' = [pc EXCEPT ![self] = "INCREMENT"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L4"]
            /\ UNCHANGED << MaxRounds, rounds, round >>

L4(self) == /\ pc[self] = "L4"
            /\ IF \A t \in Threads \ {self}: rounds[t] <= (round[self] - 2)
                  THEN /\ pc' = [pc EXCEPT ![self] = "CS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "INCREMENT"]
            /\ UNCHANGED << MaxRounds, rounds, round >>

INCREMENT(self) == /\ pc[self] = "INCREMENT"
                   /\ round' = [round EXCEPT ![self] = round[self] + 1]
                   /\ pc' = [pc EXCEPT ![self] = "WRITE"]
                   /\ UNCHANGED << MaxRounds, rounds >>

WRITE(self) == /\ pc[self] = "WRITE"
               /\ rounds' = [rounds EXCEPT ![self] = round[self]]
               /\ pc' = [pc EXCEPT ![self] = "LOCK"]
               /\ UNCHANGED << MaxRounds, round >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
            /\ UNCHANGED << MaxRounds, rounds, round >>

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ rounds' = [rounds EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "FINISH"]
                /\ UNCHANGED << MaxRounds, round >>

FINISH(self) == /\ pc[self] = "FINISH"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << MaxRounds, rounds, round >>

thread(self) == LOCK(self) \/ L1(self) \/ L2(self) \/ L3(self) \/ L4(self)
                   \/ INCREMENT(self) \/ WRITE(self) \/ CS(self)
                   \/ UNLOCK(self) \/ FINISH(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
AtMostOneCritical ==
 \A t1, t2 \in Threads:
 t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
=============================================================================
\* Modification History
\* Last modified Sun Nov 21 20:11:45 EST 2021 by Test
\* Created Sun Nov 07 16:38:08 EST 2021 by Test
