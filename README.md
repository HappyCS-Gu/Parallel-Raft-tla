# Parallel-Raft-tla
### Overview
This project is devoted to provide formal specification and verification using TLA+ for the Parallel-Raft concensus protocol proposed in *PolarFS:An ultra-low latency and failure resilient distributed file system for shared storage cloud database*.

The highlight of Parallel-Raft is that it enables "out-of-order executions". To better understand the relationship between Parallel-Raft and existing concensus algorithms(i.e. Raft,Multi-Paxos), we proposed ParallelRaft-SE(SE stands for "Sequential Execution"). Parallel-Raft is the same as Parallel-Raft except that it prohibits "out-of-order executions". In the way, we established the refinement mapping from ParallelRaft-SE to Multi-Paxos.

We discovered that Parallel-Raft, according to its brief description, neglects the so-called "ghost log entries" phenomenon, which may violate the consistency among state machines. Therefore, based on ParallelRaft-SE, we proposed ParallelRaft-CE(CE stands for "Concurrent Executions"). ParallelRaft-CE avoids the "ghost log entries" by limiting parallelism in the commmitment of log entries.

We provided the formal specifications of MultiPaxos,ParallelRaft-SE and ParallelRaft-CE and verified the refinement mapping from ParallelRaft-SE to Multi-Paxos and the correctness of ParallelRaft-CE using the TLC model checker.

### Papaers
See [paper-parallelraft](https://github.com/HappyCS-Gu/Parallel-Raft-tla/blob/master/doc/2020.8-jos.pdf)
### How to Run
Create and run TLA models in the usual way
### TLA+ Modules
`MultiPaxos.tla`: specification of Multi-Paoxs

`ParallelRaftSE`: specification of ParallelRaft-SE

`ParallelRaftCE`: specification of ParallelRaft-CE
