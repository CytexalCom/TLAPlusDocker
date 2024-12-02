-------------------------- MODULE NeedhamSchroeder --------------------------

Stati == {"Init", "WaitForMsg1", "WaitForMsg2", "WaitForMsg3", "Done"}

Agents == {"Alice", "Bob", "Intruder"}

MsgTypes == {"msg1", "msg2", "msg3"}

Nonces == {"NonceA", "NonceB", "NonceI"}

EncryptedData == [encryptedFor: Agents, data1: Nonces, data2: Agents \cup Nonces]

Messages == [receiver: Agents, type: MsgTypes, encryptedData: EncryptedData]

VARIABLES StatusA, StatusB, PartnerA, msgs, PartnerB

TypeOk == /\ StatusA \in Stati
    /\ StatusB \in Stati 
    /\ msgs \subseteq Messages

Init == /\ StatusA = "Init"
        /\ StatusB = "WaitForMsg1"
        /\ PartnerA = "Bob"
        /\ PartnerB = "Alice"
        /\ msgs = {}
        
AliceSendsMsgOne == /\ StatusA = "Init"
                    /\ StatusA' = "WaitForMsg2"
                    /\ msgs' = msgs \cup {[receiver |-> "Bob", type |-> "msg1", encryptedData |-> [encryptedFor |-> "Bob", data1 |-> "NonceA", data2 |-> "Alice"]]}
                    /\ UNCHANGED <<StatusB, PartnerB, PartnerA>>
              
                           
BobSendsMsgTwo == /\ StatusB = "WaitForMsg1"
                  /\ \E msg \in msgs : msg.receiver = "Bob"
                                     /\ msg.type = "msg1"
                                     /\ msgs' = msgs \cup {
                                        [receiver |-> "Alice", 
                                        type |-> "msg2", 
                                        encryptedData |-> [encryptedFor |-> "Alice", data1 |-> msg.encryptedData.data1, data2 |-> "NonceB"]]
                                     }
                  /\ StatusB' = "WaitForMsg3"
                  /\ UNCHANGED<<StatusA, PartnerA, PartnerB>>
                      
                    
AliceSendsMsgThree == /\ StatusA = "WaitForMsg2"
                             /\ \E msg \in msgs : msg.receiver = "Alice"
                                /\ msg.type = "msg2"
                                /\ msg.encryptedData.encryptedFor = "Alice"
                                /\ msg.encryptedData.data1 = "NonceA"
                                /\ msgs' = msgs \cup {[receiver |-> PartnerA, type |-> "msg3", encryptedData |-> [encryptedFor |-> PartnerA, data1 |-> msg.encryptedData.data2, data2 |-> "Bob"] ]}
                             /\ StatusA' = "Done"
                             /\ UNCHANGED<<StatusB, PartnerA, PartnerB>>                        

BobReceivesMsgThree == /\ StatusB = "WaitForMsg3"
                       /\ \E msg \in msgs : msg.receiver = "Bob"
                                          /\ msg.type = "msg3"
                                          /\ msg.encryptedData.encryptedFor = "Bob"
                                          /\ msg.encryptedData.data2 = "Bob"
                       /\ StatusB' = "Done"
                       /\ UNCHANGED<<StatusA, PartnerA, PartnerB, msgs>>


Next == \/ AliceSendsMsgOne
        \/ BobSendsMsgTwo
        \/ AliceSendsMsgThree
        \/ BobReceivesMsgThree 

(*The following Predicate must NOT be an Invariant, i.e., the protocol can be normally executed*)         
ProtExecFails == \neg(StatusA = "Done" /\ StatusB = "Done")

=============================================================================
\* Modification History
\* Last modified Wed Jan 10 16:24:31 CET 2024 by moritz
\* Created Wed Jan 10 14:58:34 CET 2024 by moritz
