------------------------------ MODULE TrafficLight ------------------------------
EXTENDS Naturals

VARIABLES TrafficLight, turn

(* All possible states of a traffic light *)
States == {"green", "red"}

(*Traffic Light stores all traffic lights, turn stores the currentyl active traffic light*)
(* turn = 0 -> TrafficLight[0] is active, turn = 1 -> TrafficLight[1] is active *)
vars == <<TrafficLight, turn>>

(* Init sets the initial values of the variables *)
Init ==
  /\ turn = 1
  /\ TrafficLight = [i \in 0 .. 1 |-> "red"]

(* TypeOK checks if the variables are of the correct type *)
TypeOK == /\ \A i \in 0..1: TrafficLight[i] \in States 
          /\   turn \in {0, 1}

(* Helper function to get the other traffic light *)
OtherTL(a) == (a + 1) % 2

(* Control changes the active traffic light, if the active traffic light is green *)
Control ==  /\ TrafficLight[turn] = "green"
            /\ turn' = OtherTL(turn)
            /\ UNCHANGED TrafficLight
                  
(* SwitchToRed changes the other traffic light to red *)
SwitchToRed == /\ TrafficLight[OtherTL(turn)] = "green"
               /\ TrafficLight' = [TrafficLight EXCEPT ![OtherTL(turn)] = "red"]
               /\ UNCHANGED turn

(* SwitchToGreen changes the other traffic light to green *)
SwitchToGreen == /\ TrafficLight[OtherTL(turn)] = "red"
                 /\ TrafficLight' = [TrafficLight EXCEPT ![turn] = "green"]
                 /\ UNCHANGED turn

(* All possible next states *)
Next == 
    \/ Control
    \/ SwitchToGreen
    \/ SwitchToRed
            

(* Defines all security properties *)
NeverBothGreen == TrafficLight[0] = "red" \/ TrafficLight[1] = "red"
NeverBothGreenPrime == ~(TrafficLight[0] = "green" /\ TrafficLight[1] = "green")

SwitchNotDirectlyToGreen == [][\A i \in 0..1:
                                /\ TrafficLight[i] = "green" 
                                /\ TrafficLight[OtherTL(i)] = "red"
                                =>
                                \/ TrafficLight' = TrafficLight
                                \/ TrafficLight' = [TrafficLight EXCEPT ![i] = "red"] ]_vars

SwitchOnlyAfterGreen == [][TrafficLight[turn] = "red" => turn' = turn]_vars




=============================================================================
\* Modification History
\* Last modified Wed Mar 20 15:38:46 CET 2024 by moritz
\* Created Sat Dec 30 18:44:33 CET 2023 by moritz
