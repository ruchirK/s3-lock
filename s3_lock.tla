------------------------------ MODULE s3_lock ------------------------------
EXTENDS TLC, Integers
CONSTANT Threads
(*--algorithm s3lock

variables 
    lock = "none",
    MaxRetries = 1000,
    rounds = [t \in Threads |-> 0];
  
fair process thread \in Threads
    variables round = 0, retries = 0;
begin
    \* Try to bound the size of the model?
    P0: retries := retries + 1;
        if retries > MaxRetries then
            goto FINISH;
        end if;
    P0_1: round := 0;
    
    \* Check if the lock is currently held and if so, reset ourselves.
    P1: if lock /= "none" then
    P1_1:   goto P0;
        end if;
    
    \* Check if another thread has advanced beyond us, and if so, reset ourselves.
    P2: if \E t \in Threads \ {self}: rounds[t] > round then
            goto P0;
        end if;
        
    \* If we haven't played two rounds yet then we cannot possibly win yet, try
    \* to play another round.
    P3_1: if round < 2 then
            goto P8;
          end if;
    
    \* Check if we won the last two rounds and if not, try to play another
    \* round.      
    P3_2: if \E t \in Threads \ {self}: rounds[t] > (round - 2) then
            goto P8;
         end if;
    
    \* We won the lock.    
    P4:  lock := self;
    CS:  skip;
    
    \* Unlock the lock.
    \* Note that P5 differs from the rust impl.
    P5:  rounds[self] := 0;
    P6:  lock := "none";
    
    \* Exit the game. Only here to bound the model size.
    P7:  goto FINISH;
    
    \* Try to win the next round.
    P8:  round := round + 1;
    P9:  rounds[self] := round;
    P10: goto P1;
    
    FINISH: skip;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7e5cf600" /\ chksum(tla) = "eeb3ea6f")
VARIABLES lock, MaxRetries, rounds, pc, round, retries

vars == << lock, MaxRetries, rounds, pc, round, retries >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ lock = "none"
        /\ MaxRetries = 1000
        /\ rounds = [t \in Threads |-> 0]
        (* Process thread *)
        /\ round = [self \in Threads |-> 0]
        /\ retries = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "P0"]

P0(self) == /\ pc[self] = "P0"
            /\ retries' = [retries EXCEPT ![self] = retries[self] + 1]
            /\ IF retries'[self] > MaxRetries
                  THEN /\ pc' = [pc EXCEPT ![self] = "FINISH"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P0_1"]
            /\ UNCHANGED << lock, MaxRetries, rounds, round >>

P0_1(self) == /\ pc[self] = "P0_1"
              /\ round' = [round EXCEPT ![self] = 0]
              /\ pc' = [pc EXCEPT ![self] = "P1"]
              /\ UNCHANGED << lock, MaxRetries, rounds, retries >>

P1(self) == /\ pc[self] = "P1"
            /\ IF lock /= "none"
                  THEN /\ pc' = [pc EXCEPT ![self] = "P1_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P1_1(self) == /\ pc[self] = "P1_1"
              /\ pc' = [pc EXCEPT ![self] = "P0"]
              /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P2(self) == /\ pc[self] = "P2"
            /\ IF \E t \in Threads \ {self}: rounds[t] > round[self]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P0"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "P3_1"]
            /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P3_1(self) == /\ pc[self] = "P3_1"
              /\ IF round[self] < 2
                    THEN /\ pc' = [pc EXCEPT ![self] = "P8"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P3_2"]
              /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P3_2(self) == /\ pc[self] = "P3_2"
              /\ IF \E t \in Threads \ {self}: rounds[t] > (round[self] - 2)
                    THEN /\ pc' = [pc EXCEPT ![self] = "P8"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P4"]
              /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P4(self) == /\ pc[self] = "P4"
            /\ lock' = self
            /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << MaxRetries, rounds, round, retries >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P5"]
            /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P5(self) == /\ pc[self] = "P5"
            /\ rounds' = [rounds EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "P6"]
            /\ UNCHANGED << lock, MaxRetries, round, retries >>

P6(self) == /\ pc[self] = "P6"
            /\ lock' = "none"
            /\ pc' = [pc EXCEPT ![self] = "P7"]
            /\ UNCHANGED << MaxRetries, rounds, round, retries >>

P7(self) == /\ pc[self] = "P7"
            /\ pc' = [pc EXCEPT ![self] = "FINISH"]
            /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

P8(self) == /\ pc[self] = "P8"
            /\ round' = [round EXCEPT ![self] = round[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "P9"]
            /\ UNCHANGED << lock, MaxRetries, rounds, retries >>

P9(self) == /\ pc[self] = "P9"
            /\ rounds' = [rounds EXCEPT ![self] = round[self]]
            /\ pc' = [pc EXCEPT ![self] = "P10"]
            /\ UNCHANGED << lock, MaxRetries, round, retries >>

P10(self) == /\ pc[self] = "P10"
             /\ pc' = [pc EXCEPT ![self] = "P1"]
             /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

FINISH(self) == /\ pc[self] = "FINISH"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << lock, MaxRetries, rounds, round, retries >>

thread(self) == P0(self) \/ P0_1(self) \/ P1(self) \/ P1_1(self)
                   \/ P2(self) \/ P3_1(self) \/ P3_2(self) \/ P4(self)
                   \/ CS(self) \/ P5(self) \/ P6(self) \/ P7(self)
                   \/ P8(self) \/ P9(self) \/ P10(self) \/ FINISH(self)

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
\* Last modified Sun Nov 07 19:24:48 EST 2021 by Test
\* Created Sun Nov 07 16:38:08 EST 2021 by Test
