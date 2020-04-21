-------------------------------- MODULE tem --------------------------------


EXTENDS Integers,FiniteSets,Sequences,TLC,Naturals

CONSTANTS Server

CONSTANTS Follower,Candidate,Leader,LeaderCandidate

CONSTANTS Nil

CONSTANTS  RequestVoteRequest,RequestVoteResponse,
           RequestCommitRequest,RequestCommitResponse,
           RequestSyncRequest,RequestSyncResponse,
           UpdateSyncRequest,UpdateSyncResponse
           
VARIABLE messages
VARIABLE currentTerm
VARIABLE currentState
VARIABLE votedFor
VARIABLE sync
VARIABLE endPoint
serverVars == <<currentTerm,currentState,votedFor,sync,endPoint>>


VARIABLE log
logVars == <<log>>



VARIABLE syncTrack
leaderVars == <<syncTrack>>



VARIABLE halfElections
VARIABLE elections
electionVars == <<halfElections,elections>>


VARIABLE allLogs
VARIABLE allEntries
VARIABLE allSynced



vars == <<messages,allLogs,allEntries,logVars,serverVars,leaderVars,allSynced,electionVars>>


Quorums == {i \in SUBSET(Server) : Cardinality(i)*2 > Cardinality(Server)}

Send(m) == messages' = messages \cup {m}


Value == Nat
Index == Nat
Term == Nat

Min(s) == IF s = {} THEN -1 ELSE CHOOSE i \in s : \A j \in s : j \geq i
Max(s) == IF s = {} THEN -1 ELSE CHOOSE i \in s : \A j \in s : i \geq j



InitServerVars ==  LET k == CHOOSE x \in Server : x \in Server
                   IN
                  /\ currentTerm = [i \in Server |-> 0]
                  /\ sync = [i \in Server |-> 0]
                  /\ currentState = [i \in Server |-> Follower]
                  /\ endPoint = [i \in Server |-> [n \in Term |-> <<-1,-1>>]]
                  /\ votedFor = [i \in Server |-> Nil]
                 

InitLeaderVars == /\ syncTrack = [i \in Server |-> [j \in Server |-> 0]]
                  
                           
InitHistoryVars == /\ halfElections = {}
                   /\ elections = {}
                   /\ allLogs = {}
                   /\ allEntries = {} 
                   /\ allSynced = {}           
                                                     

InitLogVars == /\ log = [i \in Server |-> [n \in Index |-> [term |-> -1,date |-> -1,
                                            value |-> Nil, committed |-> FALSE]]]

            
Init == /\ messages = {}
        /\ InitServerVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitHistoryVars

Entries == [term : Nat, index : Nat, value : Value]

TypeSafety == \*/\ allLogs \in SUBSET (SUBSET allEntries)
              /\ currentTerm \in [Server -> Nat]
              /\ currentState \in [Server -> {Follower,Leader,LeaderCandidate,Candidate}]
              /\ votedFor \in [Server -> Server \cup {Nil}]
              /\ sync \in [Server -> Nat\cup{-1}]
              /\ endPoint \in [Server -> [Term -> [date : Term \cup {-1}, index : Index \cup {-1}]]]
              /\ log \in [Server -> [Index -> [term : Index \cup {-1}, date : Term \cup {-1},
                                    value : Value \cup {Nil}, committed : {TRUE,FALSE}]]]
              /\ syncTrack \in [Server -> [Server -> Nat]]
              /\ halfElections \in [eterm : Nat, eleaderCandidate : Server, esync : Nat,
                                         evotes : Quorums, elog : SUBSET Entries]
              /\ elections \in [eterm : Nat, eleader : Server, evotes : Quorums, elog : SUBSET Entries]
             
     
logTail(s) == Max({i \in Index : s[i].term /= -1})
        
Restart(i) == 
    /\ currentState' = [currentState EXCEPT ![i] = Follower]
    /\ syncTrack' = [syncTrack EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<messages,currentTerm,endPoint,sync,votedFor,logVars,
                        electionVars,allSynced>>

Timeout(i) == 
    /\ currentState[i] \in {Follower,Candidate}
    /\ currentState' = [currentState EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i]+1]
    /\ currentTerm[i] < 4
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ UNCHANGED <<messages,leaderVars,sync,endPoint,logVars,syncTrack,
                    electionVars,allSynced>>

UpdateTerm(i) ==
    /\ \E m \in messages : 
            /\ m.mterm > currentTerm[i]
            /\ \/ m.mdest = i 
               \/ m.mdest = Nil
            /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
            /\ currentState' = [currentState EXCEPT ![i] = Follower]
            /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ UNCHANGED <<messages,sync,logVars,leaderVars,electionVars,allSynced,endPoint>>


RequestVote(i) ==
    /\ currentState[i] = Candidate
    /\ Send([ mtype |-> RequestVoteRequest,
              mterm |-> currentTerm[i],
              msync |-> sync[i],
              msource |-> i,
              mdest |-> Nil])
    /\ UNCHANGED<<serverVars,leaderVars,logVars,electionVars,allSynced>>
    
\* i: recipient
HandleRequestVoteRequest(i) == 
    /\ \E m \in messages : 
        LET j == m.msource
            syncOK == /\ m.msync \geq sync[i]
            grant == /\ syncOK
                     /\ votedFor[i] \in {Nil,j}
                     /\ currentTerm[i] = m.mterm 
        IN 
           /\ m.mterm \leq currentTerm[i]
           /\ m.mtype = RequestVoteRequest
           /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
              \/  \neg grant /\ UNCHANGED votedFor
           /\ Send([ mtype |-> RequestVoteResponse,
                     mterm |-> currentTerm[i],
                     mvoteGranted |-> grant,
                     mlog |-> LET C == {n \in Index : log[i][n].term = sync[i]}
                              IN {<<n,log[i][n]>> : n \in C},
                     mend |-> endPoint[i][m.msync],                
                     msource |-> i,
                     mdest |-> j])
           /\ UNCHANGED <<currentTerm,currentState,sync,logVars,leaderVars,
                                electionVars,allSynced,endPoint>>


Merge(entries,term,date) ==  IF entries = {} THEN [term |-> term,
                                                   date |-> date,
                                                   value |-> Nil,
                                                   committed |-> FALSE]
                        ELSE
                        LET  
                              committed == {e \in entries : e.committed = TRUE}
                              chosen == 
                             CASE committed = {} -> CHOOSE x \in entries :
                                             \A y \in entries : x.date \geq y.date
                             []   committed /= {} -> CHOOSE x \in committed : TRUE
                        IN
                            [ term |-> chosen.term,
                              date |-> date,
                              value |-> chosen.value,
                              committed |-> chosen.committed]                                 

BecomeLeaderCandidate(i) ==
    /\ currentState[i] = Candidate
    /\ \E P,Q \in Quorums :
         LET voteResponded == {m \in messages : /\ m.mtype = RequestVoteResponse
                                                /\ m.mdest = i
                                                /\ m.msource \in P
                                                /\ m.mterm = currentTerm[i]}
             voteGranted == {m \in voteResponded :  /\ m.mvoteGranted = TRUE
                                                    /\ m.msource \in Q} 
             allLog == UNION {m.mlog : m \in voteResponded}                                               
             end == LET allPoint == {m.mend : m \in voteResponded}
                        e == CHOOSE e1 \in allPoint : (\A e2 \in allPoint : e1[1] \geq e2[1])
                    IN IF e[1] = -1 THEN Max({e1[1] : e1 \in allLog})
                       ELSE e[2]
             toRecover == {n \in 0..end : log[i][n].committed = FALSE}
             toSync ==  {<<n,Merge({l[2] : l \in {t \in allLog : t[1] = n}},sync[i],currentTerm[i])>> 
                                           : n \in toRecover}
        IN
        /\ \A q \in Q : \E m \in voteGranted : m.msource = q
        /\ log' = [log EXCEPT ![i] = IF end = -1 THEN [n \in Index |-> IF log[i][n].term = sync[i] THEN 
                                                                                   [term |-> -1,
                                                                                    date |-> -1,
                                                                                    value |-> Nil,
                                                                                    committed |-> FALSE]
                                                                       ELSE log[i][n]]
                                     ELSE [n \in Index |->  IF n \in toRecover THEN 
                                                                    (CHOOSE e \in toSync : e[1] = n)[2]
                                                            ELSE IF (n > end) THEN 
                                                                    [term |-> -1,
                                                                     date |-> -1,
                                                                     value |-> Nil,
                                                                     committed |-> FALSE]
                                                            ELSE log[i][n]]]                                                              
        /\ endPoint' = [endPoint EXCEPT ![i][sync[i]] = <<currentTerm[i],end>>]
        /\ halfElections' = halfElections \union {[ eterm |-> currentTerm[i],
                                                    eleaderCandidate |-> i,
                                                    esync |-> sync[i],
                                                    evotes |-> Q,
                                                    elog |-> log[i]]}
    /\ currentState' = [currentState EXCEPT ![i] = LeaderCandidate]
    /\ syncTrack' = [syncTrack EXCEPT ![i] = [j \in Server |-> sync[i]]]
    /\ UNCHANGED<<messages,currentTerm,votedFor,sync,elections,allSynced>>    


RequestSync(i) ==
    /\ currentState[i] \in {LeaderCandidate,Leader}
    /\ \E s \in 0..sync[i] : 
            LET start == Min({n \in Index : log[i][n].term = s})
                end == Max({n \in Index : log[i][n].term = s})
            IN
                /\ Send([ mtype |-> RequestSyncRequest,
                       mterm |-> currentTerm[i],
                       msync |-> s,
                       mstart |-> start,
                       mend |-> end,
                       mentries |-> IF start = -1 THEN Nil ELSE [n \in start..end |-> log[i][n]],
                       msource |-> i,
                       mdest |-> Nil])
    /\ UNCHANGED <<serverVars,logVars,electionVars,syncTrack,allSynced>> 


HandleRequestSyncRequest(i) ==
    /\ \E m \in messages :  
                    LET  j == m.msource
                         grant == /\ m.mterm = currentTerm[i]
                                  /\ m.msync = sync[i]
                    IN 
                 /\ m.mtype = RequestSyncRequest
                 /\ m.mterm \leq currentTerm[i]
                 /\ j /= i
                 /\ \/ /\ grant
                       /\ log' = [log EXCEPT ![i] = IF m.mstart = -1 THEN 
                                                        [n \in Index |-> IF log[i][n].term = sync[i] THEN 
                                                                                    [term |-> -1,
                                                                                     date |-> -1,
                                                                                     value |-> Nil,
                                                                                     committed |-> FALSE]
                                                                         ELSE
                                                                            log[i][n]]
                                                    ELSE
                                                        [n \in Index |->  IF n < m.mstart THEN log[i][n]
                                                                          ELSE IF n \in m.mstart..m.mend 
                                                                                    THEN m.mentries[n]
                                                                          ELSE [term |-> -1,
                                                                                value |-> Nil,
                                                                                committed |-> FALSE]]]
                       /\ endPoint' = [endPoint EXCEPT ![i][sync[i]] = <<currentTerm[i],m.mend>>]
                    \/ /\ \neg grant 
                       /\ UNCHANGED <<log,endPoint>>
                 /\ Send([mtype |-> RequestSyncResponse,
                          mterm |-> currentTerm[i],
                          msyncGranted |-> grant,
                          msync |-> sync[i],
                          mstart |-> m.mstart,
                          mend |-> m.mend,
                          msource |-> i,
                          mdest |-> j])
      /\ UNCHANGED <<currentTerm,currentState,sync,votedFor,electionVars,syncTrack,allSynced>>

HandleRequestSyncResponse(i) ==
    /\ \E m \in messages :
        LET j == m.msource IN
        /\ m.mtype = RequestSyncResponse
        /\ m.mdest = i
        /\ currentTerm[i] = m.mterm
        /\ currentState[i] \in {Leader,LeaderCandidate}
        /\ syncTrack' = [syncTrack EXCEPT ![i][j] = m.msync]
        /\ \/ /\ m.msyncGranted
              /\ m.msync < sync[i]               
              /\ Send( [ mtype |-> UpdateSyncRequest,
                         mterm |-> currentTerm[i],
                         msync |-> Min({sync[i]} \union {k \in Nat : k > m.msync /\ 
                                    Cardinality({n \in Index : log[i][n].term = k})>0}),
                         msource |-> i,
                         mdest |-> {j}])
           \/ /\ \neg m.msyncGranted
              /\ UNCHANGED messages
    /\ UNCHANGED <<serverVars,logVars,electionVars,allSynced>>
      
UpdateSync(i) ==
    /\ currentState[i] = LeaderCandidate
    /\ \E Q \in Quorums :
              LET syncUpdated == {m \in messages : /\ m.mtype = RequestSyncResponse
                                                   /\ m.mterm = currentTerm[i]
                                                   /\ m.msyncGranted = TRUE
                                                   /\ m.msync = sync[i]
                                                   /\ m.msource \in Q
                                                   /\ m.mdest = i}
                  IN
                 /\ \A q \in Q : (\E m \in syncUpdated : m.msource = q) \/ q = i
                 /\  allSynced' = LET indexes == {n \in Index : log[i][n].term = sync[i]}
                                   entries == {<<n,[term |-> log[i][n].term,
                                                    date |-> log[i][n].date,
                                                    value |-> log[i][n].value,
                                                    committed |-> TRUE]>> : n \in indexes}
                                  IN allSynced \cup {<<sync[i],endPoint[i][sync[i]][2],entries>>}   
                 /\ Send( [ mtype |-> UpdateSyncRequest,
                            mterm |-> currentTerm[i],
                            msync |-> currentTerm[i],
                            msource |-> i,
                            mdest |-> Q])
    /\ UNCHANGED <<serverVars,logVars,leaderVars,electionVars>>

HandleUpdateSyncRequest(i) ==
    \E m \in messages :
        LET grant == /\ currentTerm[i] = m.mterm
                     /\ m.msync > sync[i]
            j == m.msource
        IN 
        /\ m.mtype = UpdateSyncRequest
        /\ i \in m.mdest
        /\ m.mterm \leq currentTerm[i]
        /\ \/ /\ grant
              /\ sync' = [sync EXCEPT ![i] = m.msync]                                                      
              /\ log' = [log EXCEPT ![i] = [n \in Index |-> 
                                            IF log[i][n].term = sync[i] THEN 
                                                  [term |-> log[i][n].term,
                                                   value |-> log[i][n].value,
                                                   committed |-> TRUE]
                                            ELSE log[i][n]]]
           \/ /\ \neg grant
              /\ UNCHANGED <<log,sync>>
        /\ Send([  mtype |-> UpdateSyncResponse,
                   mterm |-> currentTerm[i],
                   mupdateSyncGranted |-> grant,
                   msync |-> sync'[i],
                   msource |-> i,
                   mdest |-> j])
    /\ UNCHANGED <<currentTerm,currentState,votedFor,endPoint,leaderVars,electionVars,allSynced>>

HandleUpdateSyncResponse(i) ==
    /\ \E m \in messages :
        LET j == m.msource IN
        /\ m.mtype = UpdateSyncResponse
        /\ m.mdest = i
        /\ currentTerm[i] = m.mterm
        /\ currentState[i] \in {Leader,LeaderCandidate}
        /\ \/ /\ m.mupdateSyncGranted
              /\ syncTrack' = [syncTrack EXCEPT ![i][j] = m.msync]
           \/ /\ \neg m.mupdateSyncGranted
              /\ UNCHANGED syncTrack
    /\ UNCHANGED <<messages,serverVars,logVars,electionVars,allSynced>>

BecomeLeader(i) ==
    /\ currentState[i] = LeaderCandidate
    /\ \E Q \in Quorums : \A q \in Q : (q = i \/ syncTrack[i][q] = currentTerm[i])
                          /\ elections' = elections \union {[ eterm  |-> currentTerm[i],
                                                              esync |-> sync[i],
                                                              eleader |-> i,
                                                              evotes |-> Q,
                                                              evoterLog |-> {log[k] : k \in Q},
                                                              elog |-> log[i]]}    
    /\ sync' = [sync EXCEPT ![i] = currentTerm[i]]
    /\ currentState' = [currentState EXCEPT ![i] = Leader]
    /\ log' = [log EXCEPT ![i] = [n \in Index |-> 
                                            IF log[i][n].term = sync[i] THEN 
                                                  [term |-> log[i][n].term,
                                                   value |-> log[i][n].value,
                                                   committed |-> TRUE]
                                            ELSE log[i][n]]]       
    /\ UNCHANGED <<messages,currentTerm,votedFor,endPoint,leaderVars,halfElections,allSynced>>
                
ClientRequest(i,v) ==
    LET nextIndex ==  logTail(log[i]) + 1
            entry == [term |-> currentTerm[i],
                      value |-> v,
                      committed |-> FALSE]
    IN 
    /\ currentState[i] = Leader
    /\ logTail(log[i])<3
    /\ log' = [log EXCEPT ![i][nextIndex] = entry]
    /\ UNCHANGED <<messages,serverVars,electionVars,syncTrack,allSynced>>

CommitEntry(i,n) ==
    /\ \E Q \in Quorums: 
       LET succ == {m \in messages : /\ m.type = RequestSyncResponse
                                     /\ m.msyncGranted = TRUE
                                     /\ m.mdest = i
                                     /\ m.mterm = currentTerm[i]
                                     /\ m.msource \in Q
                                     /\ n \in m.mstart..m.mend}
       IN  /\ \A q \in Q : \E m \in succ : (m.msource = q \/ q = i)
           /\ log' = [log EXCEPT ![i][n].committed = TRUE] 
    /\ currentState[i] = Leader
    /\ UNCHANGED <<messages,serverVars,log,syncTrack,electionVars,allSynced>>
     

Next ==   /\
               \/ \E i \in Server: Restart(i)
               \/ \E i \in Server: Timeout(i)
               \/ \E i \in Server: UpdateTerm(i)
               \/ \E i \in Server: RequestVote(i)
               \/ \E i \in Server : HandleRequestVoteRequest(i)
               \/ \E i \in Server : BecomeLeaderCandidate(i)
               \/ \E i \in Server : BecomeLeader(i)
               \/ \E i \in Server, v \in Value : ClientRequest(i,v)
               \/ \E i,j \in Server : RequestSync(i)
               \/ \E i \in Server : HandleRequestSyncRequest(i)
               \/ \E i \in Server : HandleRequestSyncResponse(i)
               \/ \E i,j \in Server : UpdateSync(i)
               \/ \E i \in Server : HandleUpdateSyncRequest(i)
               \/ \E i \in Server : HandleUpdateSyncResponse(i)
           /\  allLogs' = allLogs \union {log[i] : i \in Server}
           /\  LET entries(i) == {<<n,log[i][n]>> : n \in Index} 
               IN 
               allEntries' = allEntries \union UNION {entries(i) : i \in Server}
            

AllEntries(i) == {<<n,log[i][n]>> : n \in Index} 

Lemma1 == \A i \in Server : sync[i] \leq currentTerm[i]
Lemma2 == \A i \in Server : currentState[i]=Leader => sync[i] = currentTerm[i]
Lemma3 == \A e,f \in halfElections : e.eterm = f.eterm => e.eleaderCandidate = f.eleaderCandidate
Lemma4 == \A e \in elections : \E f \in halfElections : e.eterm = f.eterm
                                         /\ e.eleader = f.eleaderCandidate
Lemma5 == \A e,f \in elections : e.eterm = f.eterm => e.eleader = f.eleader
Lemma6 == \forall i \in Server : currentState[i]=Leader => currentTerm[i] = sync[i]
Lemma7 == \A e \in halfElections : e.esync < e.eterm
Lemma8 == \A i,j \in Server, n \in Index : log[i][n].term = log[j][n].term => 
                                           log[i][n].value = log[j][n].value
Lemma9 == \A s1,s2 \in allSynced : s1[1]=s2[1] => s1=s2
Lemma10 == \A e1,e2 \in elections : e1.eterm < e2.eterm =>
            \E s \in allSynced : s[1] = e1.term
Lemma11 == LET indexes(i,t) == {n \in Index : log[i][n].term=t} 
               entries(i,t) == {<<n,log[i][n]>> : n \in indexes(i,t)} IN
            \A i \in Server : \A t \in Term :
            t < sync[i] /\ (\E e \in elections : e.eterm = t) => \E s \in allSynced : s[1] = t /\
              entries(i,t) = s[3]
Lemma12 == \A i \in Server : \A e \in AllEntries(i) :  e[2].term \leq sync[i]
Lemma13 == \A e \in halfElections : \A f \in elections : f.eterm \leq e.esync \/ f.eterm \geq e.eterm
syncCompleteness == \A i,j \in Server :  
        {e \in AllEntries(i) : e[2].term \geq 0 /\ e[2].term < Min({sync[i],sync[j]})} = 
        {e \in AllEntries(j) : e[2].term \geq 0 /\ e[2].term < Min({sync[i],sync[j]})}


Spec == Init/\ [][Next]_vars



=============================================================================
\* Modification History
\* Last modified Tue Apr 21 22:42:24 CST 2020 by assstriker
\* Created Mon Apr 06 11:17:40 CST 2020 by assstriker
