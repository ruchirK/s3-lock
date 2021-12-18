------------------------------ MODULE s3_lock_obstruction_free ------------------------------
EXTENDS TLC, Integers, Sequences
\*CONSTANT Threads
Threads == 1..3
(*--algorithm s3lock

variables 
    MaxRounds = 20,
    rounds = [t \in Threads |-> 0],
    Suspend = FALSE,
    special_thread = 1;
  
macro check_suspend() begin
    if Suspend = TRUE /\ self /= special_thread then
       goto Done;
    end if;
end macro;

macro maybe_set_suspend() begin
    either
        Suspend := TRUE;
    or
        skip;
   end either;
end macro;    

procedure suspendable_lock() begin
\* Acquire a lock over a shared resource.
LOCK:
    while TRUE do
L1:     if self /= special_thread /\ round > MaxRounds then
           goto Done;
        end if;

L1_1:        check_suspend();
L1_2:
             maybe_set_suspend();
        \* Check if another thread has advanced beyond us, and if so, reset ourselves.
L2:     if \E t \in Threads \ {self}: \A tother \in Threads: t = tother \/ rounds[t] > rounds[tother] then
            goto LOCK;
        end if;
        
L2_1:        check_suspend();
L2_2:   maybe_set_suspend();
        \* If we haven't played two rounds yet then we cannot possibly win yet, try
        \* to play another round.
L3:     if round < 2 then
            goto INCREMENT;
        end if;

L3_1:        check_suspend();
L3_2:   maybe_set_suspend();    
        \* Check if we won the last two rounds and if so, enter the critical section.
L4:     if \A t \in Threads \ {self}: rounds[t] <= (round - 2) then
            return;
        end if;
        \* Try to win the next round.
INC_1:        check_suspend();
INC_2:      maybe_set_suspend();
INCREMENT:
        round := round + 1;
W1:        check_suspend();
W2:     maybe_set_suspend();
WRITE:
        rounds[self] := round;
    end while;
    return;
end procedure;

procedure unlock() begin
\* Unlock a shared resource.
UNLOCK:
    rounds[self] := 0;
    return;
end procedure;

fair process suspenable_thread \in Threads
    variables round = 0;
begin
START_LOCK:
    call suspendable_lock();   
 \* Critical section. Only one process should make it here at a time.
CS:  skip;

    if self /= special_thread then
START_UNLOCK:
    call unlock();
    end if;

end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9f3acce1" /\ chksum(tla) = "3607ceb7")
VARIABLES MaxRounds, rounds, Suspend, special_thread, pc, stack, round

vars == << MaxRounds, rounds, Suspend, special_thread, pc, stack, round >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ MaxRounds = 20
        /\ rounds = [t \in Threads |-> 0]
        /\ Suspend = FALSE
        /\ special_thread = 1
        (* Process suspenable_thread *)
        /\ round = [self \in Threads |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "START_LOCK"]

LOCK(self) == /\ pc[self] = "LOCK"
              /\ pc' = [pc EXCEPT ![self] = "L1"]
              /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                              stack, round >>

L1(self) == /\ pc[self] = "L1"
            /\ IF self /= special_thread /\ round[self] > MaxRounds
                  THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L1_1"]
            /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, stack, 
                            round >>

L1_1(self) == /\ pc[self] = "L1_1"
              /\ IF Suspend = TRUE /\ self /= special_thread
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "L1_2"]
              /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                              stack, round >>

L1_2(self) == /\ pc[self] = "L1_2"
              /\ \/ /\ Suspend' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED Suspend
              /\ pc' = [pc EXCEPT ![self] = "L2"]
              /\ UNCHANGED << MaxRounds, rounds, special_thread, stack, round >>

L2(self) == /\ pc[self] = "L2"
            /\ IF \E t \in Threads \ {self}: \A tother \in Threads: t = tother \/ rounds[t] > rounds[tother]
                  THEN /\ pc' = [pc EXCEPT ![self] = "LOCK"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L2_1"]
            /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, stack, 
                            round >>

L2_1(self) == /\ pc[self] = "L2_1"
              /\ IF Suspend = TRUE /\ self /= special_thread
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "L2_2"]
              /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                              stack, round >>

L2_2(self) == /\ pc[self] = "L2_2"
              /\ \/ /\ Suspend' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED Suspend
              /\ pc' = [pc EXCEPT ![self] = "L3"]
              /\ UNCHANGED << MaxRounds, rounds, special_thread, stack, round >>

L3(self) == /\ pc[self] = "L3"
            /\ IF round[self] < 2
                  THEN /\ pc' = [pc EXCEPT ![self] = "INCREMENT"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L3_1"]
            /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, stack, 
                            round >>

L3_1(self) == /\ pc[self] = "L3_1"
              /\ IF Suspend = TRUE /\ self /= special_thread
                    THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "L3_2"]
              /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                              stack, round >>

L3_2(self) == /\ pc[self] = "L3_2"
              /\ \/ /\ Suspend' = TRUE
                 \/ /\ TRUE
                    /\ UNCHANGED Suspend
              /\ pc' = [pc EXCEPT ![self] = "L4"]
              /\ UNCHANGED << MaxRounds, rounds, special_thread, stack, round >>

L4(self) == /\ pc[self] = "L4"
            /\ IF \A t \in Threads \ {self}: rounds[t] <= (round[self] - 2)
                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "INC_1"]
                       /\ stack' = stack
            /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, round >>

INC_1(self) == /\ pc[self] = "INC_1"
               /\ IF Suspend = TRUE /\ self /= special_thread
                     THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "INC_2"]
               /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                               stack, round >>

INC_2(self) == /\ pc[self] = "INC_2"
               /\ \/ /\ Suspend' = TRUE
                  \/ /\ TRUE
                     /\ UNCHANGED Suspend
               /\ pc' = [pc EXCEPT ![self] = "INCREMENT"]
               /\ UNCHANGED << MaxRounds, rounds, special_thread, stack, round >>

INCREMENT(self) == /\ pc[self] = "INCREMENT"
                   /\ round' = [round EXCEPT ![self] = round[self] + 1]
                   /\ pc' = [pc EXCEPT ![self] = "W1"]
                   /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                                   stack >>

W1(self) == /\ pc[self] = "W1"
            /\ IF Suspend = TRUE /\ self /= special_thread
                  THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "W2"]
            /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, stack, 
                            round >>

W2(self) == /\ pc[self] = "W2"
            /\ \/ /\ Suspend' = TRUE
               \/ /\ TRUE
                  /\ UNCHANGED Suspend
            /\ pc' = [pc EXCEPT ![self] = "WRITE"]
            /\ UNCHANGED << MaxRounds, rounds, special_thread, stack, round >>

WRITE(self) == /\ pc[self] = "WRITE"
               /\ rounds' = [rounds EXCEPT ![self] = round[self]]
               /\ pc' = [pc EXCEPT ![self] = "LOCK"]
               /\ UNCHANGED << MaxRounds, Suspend, special_thread, stack, 
                               round >>

suspendable_lock(self) == LOCK(self) \/ L1(self) \/ L1_1(self)
                             \/ L1_2(self) \/ L2(self) \/ L2_1(self)
                             \/ L2_2(self) \/ L3(self) \/ L3_1(self)
                             \/ L3_2(self) \/ L4(self) \/ INC_1(self)
                             \/ INC_2(self) \/ INCREMENT(self) \/ W1(self)
                             \/ W2(self) \/ WRITE(self)

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ rounds' = [rounds EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << MaxRounds, Suspend, special_thread, round >>

unlock(self) == UNLOCK(self)

START_LOCK(self) == /\ pc[self] = "START_LOCK"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "suspendable_lock",
                                                             pc        |->  "CS" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "LOCK"]
                    /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, 
                                    round >>

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ IF self /= special_thread
                  THEN /\ pc' = [pc EXCEPT ![self] = "START_UNLOCK"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << MaxRounds, rounds, Suspend, special_thread, stack, 
                            round >>

START_UNLOCK(self) == /\ pc[self] = "START_UNLOCK"
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                               pc        |->  "Done" ] >>
                                                           \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "UNLOCK"]
                      /\ UNCHANGED << MaxRounds, rounds, Suspend, 
                                      special_thread, round >>

suspenable_thread(self) == START_LOCK(self) \/ CS(self)
                              \/ START_UNLOCK(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: suspendable_lock(self) \/ unlock(self))
           \/ (\E self \in Threads: suspenable_thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : /\ WF_vars(suspenable_thread(self))
                                 /\ WF_vars(suspendable_lock(self))
                                 /\ WF_vars(unlock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
AtMostOneCritical ==
 \A t1, t2 \in Threads:
 t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
 ObstructionFreedom ==
 <>[]( \E t \in Threads: \A tother \in Threads: t /= tother => rounds[t] > rounds[tother])
 
=============================================================================
\* Modification History
\* Last modified Sat Nov 27 21:11:16 EST 2021 by Test
\* Created Sat Nov 27 13:09:34 EST 2021 by Test
