--------------------------- MODULE ParallelRaftSE ---------------------------

EXTENDS Integers,FiniteSets,Sequences,TLC
CONSTANTS Server,Follower,Candidate,Leader,LeaderCandidate,Nil,Value

Quorums == {i \in SUBSET(Server) : Cardinality(i)*2 > Cardinality(Server)}
Index == {0,1,2,3,4,5,6}
Term == Nat

------------------------------------------------------------------------------
VARIABLE r1amsgs,
         r1bmsgs,
         r2amsgs,
         r2bmsgs,
         r3amsgs,
         negMsgs,
         currentTerm,
         currentState,
         vote,
         leaderLog,
         log

serverVars == <<currentTerm,currentState>>
vars == <<r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,r3amsgs,negMsgs,log,serverVars,leaderLog,vote>>

---------------------------------------------------------------------------------
Max(s) == CHOOSE i \in s : \A j \in s : i \geq j

lastIndex(i) == IF {b \in Index : log[i][b][1] /= -1} ={} 
                THEN -1   
                ELSE Max({b \in Index : log[i][b][1] /= -1}) 
                
allEntries == {<<t,v,b>> : t \in Term \cup {-1}, v \in Value \cup {Nil}, b \in {TRUE,FALSE}}
logEntries == {<<i,e>> : i \in Index, e \in allEntries}

TypeInv == /\ currentTerm \in [Server -> Nat]
           /\ currentState \in [Server -> {Follower,Leader,LeaderCandidate,Candidate}]
           /\ log \in [Server -> [Index ->  (Term \cup {-1}) \times (Value \cup {Nil}) \times BOOLEAN]]
           /\ r1amsgs \subseteq {<<t,i>> : t \in Term, i \in Server}
           /\ r1bmsgs \subseteq {<<t,e,i,j>> : t \in Term, e \in SUBSET logEntries, i \in Server, j \in Server}
           /\ r2amsgs \subseteq {<<t,n,e,i>> : t \in Term, n \in Index, e \in allEntries, i \in Server}
           /\ r2bmsgs \subseteq {<<t,n,i,j>> : t \in Term, n \in Index, i \in Server, j \in Server}
           /\ r3amsgs \subseteq {<<t,n,i>> : t \in Term, n \in Index, i \in Server}
           /\ negMsgs \subseteq {<<t,i>> : t \in Term, i \in Server}
           /\ log \in [Server -> [Index -> allEntries]]
           /\ leaderLog \in [Term -> [Index -> allEntries]]
           /\ vote \in [Server -> [Index -> [Term -> Value \cup {Nil}]]]

---------------------------------------------------------------------------------------
InitServerVars ==  LET k == CHOOSE x \in Server : x \in Server
                   IN
                  /\ currentTerm = [i \in Server |-> 0]
                  /\ currentState = [i \in Server |-> Follower]          
                                                    
InitLogVars == /\ log = [i \in Server |-> [j \in Index |-> <<-1,Nil,FALSE>>]]    

Init == /\ r1amsgs = {}
        /\ r1bmsgs = {}
        /\ r2amsgs = {}
        /\ r2bmsgs = {}
        /\ r3amsgs = {}
        /\ negMsgs = {}
        /\ vote = [i \in Server |-> [b \in Index |-> [t \in Term |-> Nil]]]
        /\ leaderLog = [i \in Term |-> [j \in Index |-> <<-1,Nil,FALSE>>]]     
        /\ InitServerVars
        /\ InitLogVars
        
-------------------------------------------------------------------------------------     
Restart(i) == 
    /\ currentState' = [currentState EXCEPT ![i] = Follower]
    /\ UNCHANGED <<r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,r3amsgs,negMsgs,
                    currentTerm,log,leaderLog,vote>>
UpdateTerm(i,b) == 
    /\ currentTerm[i] < b
    /\ currentTerm' = [currentTerm EXCEPT ![i] = b]
    /\ currentState' = [currentState EXCEPT ![i] = Follower]

ReceiveHighTerm(i) ==
    /\ \E m \in negMsgs : 
            /\ m[1] > currentTerm[i]
            /\ m[2] = i 
            /\ UpdateTerm(i,m[1])
    /\ UNCHANGED <<log,r1amsgs,r2amsgs,r1bmsgs,r2bmsgs,r3amsgs,
                    negMsgs,leaderLog,vote>>

Timeout(i) == 
    /\ currentState[i] \in {Follower,Candidate}
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ currentState' = [currentState EXCEPT ![i] = Candidate]
    /\ currentTerm[i] + 1 \in Nat
    /\ UNCHANGED <<r1amsgs,r1bmsgs,log,r2amsgs,r2bmsgs,r3amsgs,
                        negMsgs,leaderLog,vote>>
    
RequestVote(i) ==
    /\ currentState[i] = Candidate
    /\ r1amsgs' = r1amsgs \cup {<<currentTerm[i],i>>}
    /\ UNCHANGED <<serverVars,r1bmsgs,log,r2amsgs,r2bmsgs,r3amsgs,
                        negMsgs,leaderLog,vote>>
    
\* i: recipient
HandleRequestVoteRequest(i) == 
    /\ \E m \in r1amsgs : 
        LET j == m[2]
            grant ==  m[1] > currentTerm[i]
            entries == {<<n,log[i][n]>> : n \in Index}
        IN 
          \/ /\ grant
             /\ UpdateTerm(i,m[1])
             /\ r1bmsgs' = r1bmsgs \cup {<<m[1],entries,i,j>>}
             /\ UNCHANGED negMsgs
          \/ /\ \neg grant
             /\ negMsgs' = negMsgs \cup {<<currentTerm[i],j>>}
             /\ UNCHANGED <<currentState,currentTerm,r1bmsgs>>
    /\ UNCHANGED <<log,r1amsgs,r2amsgs,r2bmsgs,r3amsgs,vote,leaderLog>> 
 
                          
Merge(entries,term,v) ==  
                          LET  
                          committed == {e \in entries : e[3] = TRUE}
                          chosen == 
                         CASE committed = {} -> CHOOSE x \in entries : \A y \in entries : x[1] \geq y[1]
                         []   committed /= {} -> CHOOSE x \in committed : TRUE
                          safe == IF chosen[2] = Nil THEN v ELSE chosen[2]
                          IN  <<term,safe,chosen[3]>>                           
                                    
BecomeLeaderCandidate(i) ==
    /\ currentState[i] = Candidate
    /\ \E Q \in Quorums :
         LET voteGranted == {m \in r1bmsgs : m[4] = i /\ m[3] \in Q /\ m[1] = currentTerm[i]}
             allLog == UNION {m[2] : m \in voteGranted}
             valid == {e \in allLog : e[2][1] /= -1}             
             end == IF valid = {} THEN -1 ELSE Max({e[1] : e \in valid})
        IN
        /\ \A q \in Q : \E m \in voteGranted : m[3] = q 
        /\ \E v \in Value : leaderLog' = [leaderLog EXCEPT ![currentTerm[i]] =  [n \in Index |-> IF n \in 0..end THEN
                 Merge({l[2] : l \in {t \in allLog : t[1] = n}},currentTerm[i],v) ELSE <<-1,Nil,FALSE>>]]
    /\ currentState' = [currentState EXCEPT ![i] = LeaderCandidate]
    /\ UNCHANGED<<currentTerm,r1amsgs,r2amsgs,r1bmsgs,r2bmsgs,r3amsgs,negMsgs,log,vote>>    
 
RequestSync(i) ==
    /\ currentState[i] \in {LeaderCandidate,Leader}
    /\ LET sync == {n \in Index : leaderLog[currentTerm[i]][n][1] /= -1} IN
       \E n \in sync : r2amsgs' = r2amsgs \cup {<<currentTerm[i],n,leaderLog[currentTerm[i]][n],i>>}
    /\ UNCHANGED <<serverVars,log,r1amsgs,r1bmsgs,r2bmsgs,r3amsgs,negMsgs,leaderLog,vote>> 

HandleRequestSyncRequest(i) ==
    /\ \E m \in r2amsgs :  
                    LET  j == m[4]
                         grant == m[1] \geq currentTerm[i]
                    IN 
                 /\ \/ /\ m[1] > currentTerm[i]
                       /\ UpdateTerm(i,m[1])
                    \/ /\ m[1] \leq currentTerm[i]
                       /\ UNCHANGED <<currentTerm,currentState>>  
                 /\ \/ /\ grant
                       /\ log' = [log EXCEPT ![i][m[2]] = m[3]]
                       /\ vote' = [vote EXCEPT ![i][m[2]][m[1]] = m[3][2]]
                       /\ r2bmsgs ' = r2bmsgs \cup {<<m[1],m[2],i,j>>}
                       /\ UNCHANGED negMsgs         
                    \/ /\ \neg grant 
                       /\ negMsgs' = negMsgs \cup {<<currentTerm[i],j>>}
                       /\ UNCHANGED <<vote,r2bmsgs,log>>
   /\ UNCHANGED <<r1amsgs,r1bmsgs,r2amsgs,r3amsgs,leaderLog>>
  
CommitEntry(i) ==
    /\ \E index \in Index , Q \in Quorums :
        LET  syncSuccess == { m \in r2bmsgs :  m[4] = i /\ m[3] \in Q /\ 
                                               m[1] = currentTerm[i] /\ m[2] = index}
        IN
        /\ currentState[i] \in {Leader,LeaderCandidate}
        /\ \A q \in Q : \E m \in syncSuccess : m[3] = q
        /\ leaderLog' = [leaderLog EXCEPT ![currentTerm[i]][index][3] = TRUE]
    /\ UNCHANGED <<serverVars,log,r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,r3amsgs,negMsgs,vote>>
                                                   
RequestCommit(i) ==
    /\ currentState[i] \in {Leader,LeaderCandidate}
    /\ LET committed == {n \in Index : leaderLog[currentTerm[i]][n][3] = TRUE} IN
        \E n \in committed : r3amsgs' = r3amsgs \cup {<<currentTerm[i],n,i>>}
    /\ UNCHANGED <<serverVars,log,r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,negMsgs,leaderLog,vote>>

HandleRequestCommitRequest(i) ==
    /\ \E m \in r3amsgs :
        LET grant == currentTerm[i] \leq  m[1]
            j == m[3]
        IN
        /\ \/ /\ m[1] > currentTerm[i]
              /\ UpdateTerm(i,m[1])
           \/ /\ m[1] \leq currentTerm[i]
              /\ UNCHANGED <<currentTerm,currentState>>  
        /\ \/ /\ grant
              /\ log[i][m[2]][1] = m[1]
              /\ log' = [log EXCEPT ![i][m[2]][3] = TRUE]
              /\ UNCHANGED negMsgs
           \/ /\ \neg grant
              /\ negMsgs' = negMsgs \cup {<<currentTerm[i],j>>}
              /\ UNCHANGED log
    /\ UNCHANGED <<serverVars,r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,r3amsgs,leaderLog,vote>>  

BecomeLeader(i) ==
    /\ currentState[i] = LeaderCandidate
    /\ currentState' = [currentState EXCEPT ![i] = Leader]
    /\ UNCHANGED <<currentTerm,log,r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,r3amsgs,
                    negMsgs,leaderLog,vote>>
                
ClientRequest(i) ==
    LET ind == {b \in Index : leaderLog[currentTerm[i]][b][1] /= -1} 
        nextIndex ==  IF ind ={} 
                THEN 0
                ELSE Max(ind) + 1
    IN 
    /\ currentState[i] = Leader
    /\ nextIndex \in Index
    /\ \E v \in Value :leaderLog' = [leaderLog EXCEPT ![currentTerm[i]][nextIndex] = 
                                                           <<currentTerm[i],v,FALSE>>]
    /\ UNCHANGED <<serverVars,log,r1amsgs,r1bmsgs,r2amsgs,r2bmsgs,r3amsgs,negMsgs,vote>>

Next == \/ \E i \in Server: Restart(i)
        \/ \E i \in Server: Timeout(i)
        \/ \E i \in Server: ReceiveHighTerm(i)
        \/ \E i \in Server: RequestVote(i)
        \/ \E i \in Server : HandleRequestVoteRequest(i)
        \/ \E i \in Server : BecomeLeaderCandidate(i)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server : CommitEntry(i)
        \/ \E i \in Server : ClientRequest(i)
        \/ \E i,j \in Server : RequestCommit(i)
        \/ \E i \in Server : HandleRequestCommitRequest(i)
        \/ \E i,j \in Server : RequestSync(i)
        \/ \E i \in Server : HandleRequestSyncRequest(i)
               

Inv == /\ TypeInv

------------------------------------------------------------------------------------------------
Acceptors == Server
Ballots == Term
Instances == Index
ballot == currentTerm
leaderVote == [i \in Ballots |-> [j \in Index |-> <<leaderLog[i][j][1],leaderLog[i][j][2]>>]]
1amsgs == {<<m[1]>>: m \in r1amsgs}
1bmsgs == {<<m[1],{<<e[1],<<e[2][1],e[2][2]>> >> : e \in m[2]},m[3]>> : m \in r1bmsgs}
2amsgs == {<<m[1],m[2],<<m[3][1],m[3][2]>> >>: m \in r2amsgs}

Spec == Init /\ [][Next]_vars 

A == INSTANCE MultiPaxos

THEOREM  Refinement == Spec => A!Spec


=============================================================================
\* Modification History
\* Last modified Wed Sep 09 15:26:16 CST 2020 by 15150

