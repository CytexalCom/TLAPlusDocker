-------------------------- MODULE NeedhamSchroeder --------------------------

Stati == {"Init", "WaitForMsg1", "WaitForMsg2", "WaitForMsg3", "Done"}

Agents == {"Alice", "Bob", "Intruder"}

MsgTypes == {"msg1", "msg2", "msg3"}

Nonces == {"NonceA", "NonceB", "NonceI"}

EncryptedData == [encryptedFor: Agents, data1: Nonces, data2: Agents \cup Nonces]

Messages == [receiver: Agents, type: MsgTypes, encryptedData: EncryptedData]

VARIABLES StatusA, StatusB, PartnerA, msgs

TypeOk == /\ StatusA \in Stati
    /\ StatusB \in Stati 
    /\ msgs \subseteq Messages

Init == /\ StatusA = "Init"
        /\ StatusB = "WaitForMsg1"
        /\ PartnerA = "Bob"
        /\ msgs = {}
        
AliceSendsMsgOne == /\ StatusA = "Init"
                    /\ StatusA' = "WaitForMsg2"
                    /\ \E Agent \in Agents: PartnerA' = Agent
                        /\ msgs' = msgs \cup { [receiver |-> Agent, type |-> "msg1", encryptedData |-> [encryptedFor |-> Agent, data1 |-> "NonceA", data2 |-> "Alice"]] }
                    /\ UNCHANGED<<StatusB>>                        
                           
BobSendsMsgTwo == /\ StatusB = "WaitForMsg1"
                  /\ \E msg \in msgs : msg.receiver = "Bob"
                                     /\ msg.type = "msg1"
                                     /\ msg.encryptedData.encryptedFor = "Bob"
                                     /\ StatusB' = "WaitForMsg3"
                                     /\ msgs' = msgs \cup { [receiver |-> "Alice", type |-> "msg2", encryptedData |-> [encryptedFor |-> "Alice", data1 |-> msg.encryptedData.data1, data2 |-> "NonceB"]] }
                  /\ UNCHANGED <<StatusA, PartnerA>>                      
                    
AliceSendsMsgThree == /\ StatusA = "WaitForMsg2"
                             /\ \E msg \in msgs : msg.receiver = "Alice"
                                /\ msg.type = "msg2"
                                /\ msg.encryptedData.encryptedFor = "Alice"
                                /\ msg.encryptedData.data1 = "NonceA"
                                /\ msgs' = msgs \cup {[receiver |-> PartnerA, type |-> "msg3", encryptedData |-> [encryptedFor |-> PartnerA, data1 |-> msg.encryptedData.data2, data2 |-> "Bob"] ]}
                             /\ StatusA' = "Done"
                             /\ UNCHANGED<<StatusB, PartnerA>>                        

BobReceivesMsgThree == /\ StatusB = "WaitForMsg3"
                       /\ \E msg \in msgs : msg.receiver = "Bob"
                                          /\ msg.type = "msg3"
                                          /\ msg.encryptedData.encryptedFor = "Bob"
                                          /\ msg.encryptedData.data2 = "Bob"
                                          /\ StatusB' = "Done"
                       /\ UNCHANGED <<StatusA, PartnerA, msgs>>

Next == \/ AliceSendsMsgOne
        \/ BobSendsMsgTwo
        \/ AliceSendsMsgThree
        \/ BobReceivesMsgThree 

(*The following Predicate must NOT be an Invariant, i.e., the protocol can be normally executed*)         
ProtExecFails == \neg(StatusA = "Done" /\ StatusB = "Done")             

=============================================================================
