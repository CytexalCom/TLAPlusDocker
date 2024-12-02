----------------------- MODULE NeedhamSchroederAttack -----------------------

(**
   a) Your task is to complete the holes in the module and formulate the invariants stated below. Then check the invariants.
   b) Not all invariants that shall hold do hold. The trace, that violate at least one of the invariants reveals an attack on the authentication protocol. How does the attack work?
   c) Fix the protocol, such that the attack does not work any more. Check that alle the invariants supposed to be valid for the protocol indeed do hold for the fixed version of the protocol.  
**)

Stati == {"Init", "WaitForMsg1", "WaitForMsg2", "WaitForMsg3", "Done"}

Agents == {"Alice", "Bob", "Intruder"}

MsgTypes == {"msg1", "msg2", "msg3"}

Nonces == {"NonceA", "NonceB", "NonceI"}

EncryptedData == [encryptedFor: Agents, data1: Nonces, data2: Agents \cup Nonces \cup {""}]

Messages == [receiver: Agents, type: MsgTypes, encryptedData: EncryptedData]

VARIABLES StatusA, StatusB, PartnerA, PartnerB, msgs, IntruderKnowsNonceA, IntruderKnowsNonceB

TypeOk == /\ StatusA \in Stati
    /\ StatusB \in Stati 
    /\ msgs \subseteq Messages
    /\ PartnerA \in Agents
    /\ PartnerB \in Agents
    /\ IntruderKnowsNonceA \in {TRUE, FALSE}
    /\ IntruderKnowsNonceB \in {TRUE, FALSE}

Init == /\ StatusA = "Init"
        /\ StatusB = "WaitForMsg1"
        /\ PartnerA = "Bob"
        /\ PartnerB = "Alice"
        /\ IntruderKnowsNonceA = FALSE
        /\ IntruderKnowsNonceB = FALSE
        /\ msgs = {}
        
AliceSendsMsgOne == /\ StatusA = "Init"
                    /\ StatusA' = "WaitForMsg2"
                    /\ \E Agent \in {"Bob", "Intruder"}: PartnerA' = Agent
                        /\ msgs' = { [receiver |-> Agent, type |-> "msg1", encryptedData |-> [encryptedFor |-> Agent, data1 |-> "NonceA", data2 |-> "Alice"]] }
                    /\ UNCHANGED<<StatusB, PartnerB, IntruderKnowsNonceA, IntruderKnowsNonceB>>                        
                           
BobSendsMsgTwo == 
  /\ StatusB = "WaitForMsg1"
  /\ \E msg \in msgs : msg.receiver = "Bob"
     /\ msg.type = "msg1"
     /\ msg.encryptedData.encryptedFor = "Bob"
     /\ msgs' = msgs \cup {[receiver |-> "Alice", type |-> "msg2", encryptedData |-> [encryptedFor |-> "Alice", data1 |-> msg.encryptedData.data1, data2 |-> "Bob"]]}
  /\ StatusB' = "WaitForMsg3"
  /\ UNCHANGED<<StatusA, PartnerA>>


                    
AliceSendsMsgThree == 
  /\ StatusA = "WaitForMsg2"
  /\ \E msg \in msgs : msg.receiver = "Alice"
     /\ msg.type = "msg2"
     /\ msg.encryptedData.encryptedFor = "Alice"
     /\ msg.encryptedData.data1 = "NonceA"
     /\ msg.encryptedData.data2 = "Bob"
  /\ msgs' = msgs \cup {[receiver |-> PartnerA, type |-> "msg3", encryptedData |-> [encryptedFor |-> PartnerA, data1 |-> msg.encryptedData.data2, data2 |-> "Bob"]]}
  /\ StatusA' = "Done"
  /\ UNCHANGED<<StatusB, PartnerA>>
                

BobReceivesMsgThree ==
  /\ StatusB = "WaitForMsg3"
  /\ \E msg \in msgs : msg.receiver = "Bob"
     /\ msg.type = "msg3"
     /\ msg.encryptedData.encryptedFor = "Bob"
     /\ msg.encryptedData.data1 = "NonceB"
  /\ StatusB' = "Done"
  /\ UNCHANGED<<StatusA, PartnerA>>

IntruderLearnsNonceA ==
  /\ \E msg \in msgs : msg.receiver = "Intruder"
     /\ msg.encryptedData.data1 = "NonceA"
  /\ IntruderKnowsNonceA' = TRUE
  /\ UNCHANGED<<StatusA, StatusB, PartnerA, PartnerB, msgs, IntruderKnowsNonceB>>

IntruderLearnsNonceB ==
  /\ \E msg \in msgs : msg.receiver = "Intruder"
     /\ msg.encryptedData.data2 = "NonceB"
  /\ IntruderKnowsNonceB' = TRUE
  /\ UNCHANGED<<StatusA, StatusB, PartnerA, PartnerB, msgs, IntruderKnowsNonceA>>

                        
IntruderCatchesAndForwardsMessage == \E Agent \in Agents : \E msg \in msgs : msgs' = {[receiver |-> Agent, type |-> msg.type, encryptedData |-> msg.encryptedData]}
                        /\ UNCHANGED<<StatusA, StatusB, PartnerA, PartnerB, IntruderKnowsNonceA, IntruderKnowsNonceB>>                          

KnownNonces == IF IntruderKnowsNonceA THEN (IF IntruderKnowsNonceB  THEN {"NonceI", "NonceA", "NonceB"} ELSE {"NonceI", "NonceA"}) ELSE (IF IntruderKnowsNonceB  THEN {"NonceI", "NonceB"} ELSE {"NonceI"})  

IntruderSendsMessageOne ==
  /\ msgs' = msgs \cup {[receiver |-> "Bob", type |-> "msg1", encryptedData |-> [encryptedFor |-> "Bob", data1 |-> "NonceI", data2 |-> "Intruder"]]}
  /\ UNCHANGED<<StatusA, StatusB, PartnerA, PartnerB, IntruderKnowsNonceA, IntruderKnowsNonceB>>
                                                
IntruderSendsMessageTwo ==
  /\ msgs' = msgs \cup {[receiver |-> "Alice", type |-> "msg2", encryptedData |-> [encryptedFor |-> "Alice", data1 |-> "NonceI", data2 |-> "NonceB"]]}
  /\ UNCHANGED<<StatusA, StatusB, PartnerA, PartnerB, IntruderKnowsNonceA, IntruderKnowsNonceB>>
     

IntruderSendsMessageThree ==
  /\ \E msg \in msgs : msg.receiver = "Intruder"
     /\ msg.type = "msg2"
     /\ msg.encryptedData.encryptedFor = "Intruder"
     /\ msg.encryptedData.data2 = "NonceB"
  /\ msgs' = msgs \cup {[receiver |-> "Bob", type |-> "msg3", encryptedData |-> [encryptedFor |-> "Bob", data1 |-> msg.encryptedData.data2, data2 |-> "Intruder"]]}
  /\ UNCHANGED<<StatusA, StatusB, PartnerA, PartnerB, IntruderKnowsNonceA, IntruderKnowsNonceB>>


AliceAuthenticatesWithBobIffBobAuthenticatesWithAlice ==
  (StatusA = "Done" /\ StatusB = "Done") => PartnerA = "Bob" /\ PartnerB = "Alice"


  IntruderDoesNotKnowNonceA ==
  IntruderKnowsNonceA = FALSE \/ PartnerA = "Intruder"

IntruderDoesNotKnowNonceB ==
  IntruderKnowsNonceB = FALSE \/ PartnerB = "Intruder"

AliceAuthenticatesWithBobIffBobAuthenticatesWithAlice ==
  (StatusA = "Done" /\ StatusB = "Done") => PartnerA = "Bob" /\ PartnerB = "Alice"


Next == \/ AliceSendsMsgOne
        \/ BobSendsMsgTwo
        \/ AliceSendsMsgThree
        \/ BobReceivesMsgThree
        \/ IntruderLearnsNonceA
        \/ IntruderLearnsNonceB
        \/ IntruderCatchesAndForwardsMessage
        \/ IntruderSendsMessageOne
        \/ IntruderSendsMessageTwo
        \/ IntruderSendsMessageThree
         
(*The following Statepredicate must NOT be an Invariant, i.e., the protocol can be normally executed*)         
ProtExecFails == \neg(StatusA = "Done" /\ StatusB = "Done")
             
(*IntruderDoesNotKnowNonceA == Todo: formulate an invariant, stating that the Intruder does not get to know the nonce of Alice if Alice does not authenticate with the intruder*)
(*IntruderDoesNotKnowNonceB == Todo: formulate an invariant, stating that the Intruder does not get to know the nonce of Bob if Bob does not authenticate with the intruder *)

(*AliceAuthenticedWithBobIffBobAuthenticatedWithAlice == Todo: formulate an invariant, stating that if Alice and Bob both completed the Protocol successfully, then Alice authenticated with Bob if and only if Bob authenticated with Alice*)

=============================================================================
\* Modification History
\* Last modified Wed Jan 10 21:51:12 CET 2024 by moritz
\* Created Wed Jan 10 21:38:58 CET 2024 by moritz
