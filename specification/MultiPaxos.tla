----------------------------- MODULE MultiPaxos -----------------------------

EXTENDS Integers, FiniteSets
    
CONSTANTS Acceptors,Nil,Value

Ballots == Nat
Instances == {0,1,2,3,4,5,6}
Quorums == {Q \in SUBSET Acceptors : Cardinality(Q) > Cardinality(Acceptors) \div 2}
Max(s) == CHOOSE x \in s : \forall y \in s : x \geq y

-------------------------------------------------------------------------------
VARIABLES ballot, 
          vote, 
          leaderVote,
          1amsgs, 
          1bmsgs, 
          2amsgs
          
--------------------------------------------------------------------------------    
Init ==
    /\  ballot = [a \in Acceptors |-> 0]
    /\  vote = [a \in Acceptors |-> 
            [i \in Instances |-> 
                [b \in Ballots |-> Nil]]]
    /\  1amsgs = {}
    /\  1bmsgs = {}
    /\  2amsgs = {}
    /\  leaderVote = [b \in Ballots |-> [i \in Instances |-> <<-1,Nil>>]]
    
----------------------------------------------------------------------------------    

allEntries == {<<i,<<b,v>> >> : i \in Instances, b \in Ballots \cup {-1}, v \in Value \cup {Nil}}

TypeInv ==
    /\  ballot \in [Acceptors -> {-1} \cup Ballots]
    /\  leaderVote \in [Ballots -> [Instances -> ({-1} \cup Ballots) \times ({Nil} \cup Value)]]
    /\  vote \in [Acceptors -> [Instances ->  [Ballots -> ({Nil} \cup Value )]]]
    /\  1amsgs \subseteq {<<b>> : b \in Ballots}
 \*   /\  1bmsgs \subseteq {<<b, e, a>> : b \in Ballots, a \in Acceptors, e \in SUBSET allEntries}
    /\  2amsgs \subseteq {<<b, i, <<bb,v>>>> : i \in Instances, b \in Ballots, bb \in Ballots,v \in Value \cup {Nil}}
    /\  leaderVote \in [Ballots -> [Instances -> ((Ballots\cup {-1}) \times ({Nil} \cup Value))]]

------------------------------------------------------------------------------------
IncreaseBallot(a,b) ==
    /\ ballot[a] < b
    /\ ballot' = [ballot EXCEPT ![a] = b]
    /\ UNCHANGED <<vote, leaderVote, 1amsgs, 1bmsgs, 2amsgs>>

Phase1a(b) ==
    /\  1amsgs' = 1amsgs \cup {<<b>>}
    /\  UNCHANGED <<ballot, vote, leaderVote,1bmsgs, 2amsgs>>

MaxAcceptorVote(a, i) ==
  LET maxBallot == Max({b \in Ballots : vote[a][i][b] # Nil} \cup {-1})
      v == IF maxBallot > -1 THEN vote[a][i][maxBallot] ELSE Nil
  IN <<maxBallot, v>>

Phase1b(a, b) ==
    /\  ballot[a] < b
    /\  <<b>> \in 1amsgs
    /\  ballot' = [ballot EXCEPT ![a] = b]
    /\  1bmsgs' = 1bmsgs \cup 
            {<<b, {<<i,MaxAcceptorVote(a,i)>> : i \in Instances}, a>>}
    /\  UNCHANGED <<vote, leaderVote, 1amsgs, 2amsgs>>
    
1bMsgs(b,  Q) ==
    {m \in 1bmsgs :  m[3] \in Q  /\ m[1] = b}


  
MaxVote(b, i, Q) ==
    LET entries == UNION{m[2] : m \in 1bMsgs(b,Q)}
        ientries == {e \in entries : e[1] = i}
        maxBal == Max({e[2][1] : e \in ientries})
    IN  CHOOSE v \in Value \cup {Nil}  : \E e \in ientries :   
            /\ e[2][1] = maxBal /\ e[2][2] = v 


                      
lastInstance(b,Q) == LET entries == UNION{m[2] : m \in 1bMsgs(b,Q)}
                         valid == {e \in entries : e[2][1] /= -1}
                     IN 
                     IF valid = {} THEN -1 ELSE Max({e[1] : e \in valid})


            
Merge(b) == /\ \E Q \in Quorums :
                /\ \A a \in Q : \E m \in 1bMsgs(b,Q) : m[3] = a
                /\ \E v \in Value : leaderVote' = [leaderVote EXCEPT ![b] = [i \in Instances |-> 
                            IF (i \in 0..lastInstance(b,Q) /\ leaderVote[b][i][1] = -1)
                     \*       THEN <<b,MaxVote(b,i,Q)>>
                            THEN IF MaxVote(b,i,Q) = Nil THEN <<b,v>>
                                  ELSE <<b,MaxVote(b,i,Q)>>
                            ELSE leaderVote[b][i]]]
            /\ UNCHANGED <<vote, ballot, 1amsgs, 1bmsgs, 2amsgs>>            
            

Propose(b,i) == /\ leaderVote[b][i][1] = -1
                /\ \E Q \in Quorums :
                    /\ \A a \in Q : \E m \in 1bMsgs(b,Q) : m[3] = a
                    /\ \E v \in Value : leaderVote'=[leaderVote EXCEPT ![b][i] = IF MaxVote(b,i,Q) = Nil
                                                                                 THEN <<b,v>>
                                                                                 ELSE <<b,MaxVote(b,i,Q)>>]                                
               /\ UNCHANGED <<vote, ballot, 1amsgs, 1bmsgs, 2amsgs>>                                                                                  

Phase2a(b, i) ==
    /\ leaderVote[b][i][1] = b
    /\ 2amsgs' = 2amsgs \cup {<<b, i, leaderVote[b][i]>>}
    /\ UNCHANGED <<ballot, vote, leaderVote, 1amsgs, 1bmsgs>>

Vote(a, b, i) ==
    /\ ballot[a] \leq  b
    /\ ballot' = [ballot EXCEPT ![a] = b]
    /\  \E m \in 2amsgs : 
            /\ m[2] = i /\ m[1] = b
            /\ vote' = [vote EXCEPT ![a][i][b] = m[3][2]]
    /\  UNCHANGED <<leaderVote, 1amsgs, 1bmsgs, 2amsgs >>
    
Next == 
    \/  \E a \in Acceptors, b \in Ballots : IncreaseBallot(a,b)
    \/  \E b \in Ballots : Phase1a(b)
    \/  \E a \in Acceptors, b \in Ballots : Phase1b(a,b)
    \/  \E b \in Ballots : Merge(b)
    \/  \E b \in Ballots, i \in Instances : Propose(b,i)
    \/  \E b \in Ballots, i \in Instances : Phase2a(b,i)
    \/  \E a \in Acceptors, b \in Ballots, i \in Instances : Vote(a, b, i)
    
Spec == Init /\ [][Next]_<<leaderVote, ballot, vote, 1amsgs, 1bmsgs, 2amsgs>>
----------------------------------------------------------------------------------------
Conservative(i,b) ==
    \A a1,a2 \in Acceptors :
        LET v1 == vote[a1][i][b]
            v2 == vote[a2][i][b]
        IN  (v1 # Nil /\ v2 # Nil) => v1 = v2

ConservativeVoteArray ==
    \A i \in Instances : \A b \in Ballots :
        Conservative(i,b)

WellFormed == \A a \in Acceptors : \A i \in Instances : \A b \in Ballots :
    b > ballot[a] => vote[a][i][b] = Nil
       
VotedFor(a,i,b,v) == vote[a][i][b] = v

ChosenAt(i,b,v) ==
    \E Q \in Quorums : \A a \in Q : VotedFor(a,i,b,v)

Chosen(i,v) ==
    \E b \in Ballots : ChosenAt(i,b,v)

Choosable(v, i, b) ==
    \E Q \in Quorums : \A a \in Q : ballot[a] > b => vote[a][i][b] = v
    
SafeAt(v, i, b) ==
    \A b2 \in Ballots : \A v2 \in Value : 
        (b2 < b /\ Choosable(v2, i, b2))
        => v = v2
        
SafeInstanceVoteArray(i) == \A b \in Ballots : \A a \in Acceptors :
    LET v == vote[a][i][b]
    IN  v # Nil => SafeAt(v, i, b)

SafeVoteArray == \A i \in Instances : SafeInstanceVoteArray(i)

Inv == TypeInv /\ WellFormed /\ SafeVoteArray /\ ConservativeVoteArray

Correctness ==  
    \A i \in Instances : \A v1,v2 \in Value :
        Chosen(i, v1) /\ Chosen(i, v2) => v1 = v2 

=============================================================================
\* Modification History
\* Last modified Wed Sep 09 15:26:35 CST 2020 by 15150

