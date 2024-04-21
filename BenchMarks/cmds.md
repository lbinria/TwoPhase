### Commands

#### BFS (for 4 RMs)
`KeyValueStore/spec > TRACE_PATH=../BenchMarks/trace.ndjson.4RM.VEA CONFIG_PATH=../BenchMarks/conf.4RM.ndjson java -XX:+UseParallelGC  -cp '/Users/cirstea/bin/TLA/tla2tools.jar' tlc2.TLC -note TwoPhaseTrace.tla`

#### DFS (for 4 RMs)
`KeyValueStore/spec > TRACE_PATH=../BenchMarks/trace.ndjson.4RM.VEA CONFIG_PATH=../BenchMarks/conf.4RM.ndjson java -XX:+UseParallelGC -Dtlc2.tool.queue.IStateQueue=StateDeque -cp '/Users/cirstea/bin/TLA/tla2tools.jar' tlc2.TLC -note TwoPhaseTrace.tla`

#### Script

Alternatively, run the script `tla_trace_validation.py` on one of the trace files (the trace file should be consistent with the conf file:
`trace.ndjson.4RM.VEA` with  `conf.4RM.ndjson`, and `-Dtlc2.tool.queue.IStateQueue=StateDeque` should be added in the script if DFS is to be used).

`spec > python tla_trace_validation.py --trace BenchMarks/trace.ndjson.4RM.VEA  --config BenchMarks/conf.4RM.ndjson spec/TwoPhaseTrace.tla`


### Benchmarks

#### Valid traces for 4, 8, 12, 16 RMs
- trace.ndjson.4RM.VEA
- trace.ndjson.8RM.VEA
- trace.ndjson.12RM.VEA
- trace.ndjson.16RM.VEA

#### Invalid traces for 4 and 16 RMs 
- trace.ndjson.BUG-16RM.VEA (use conf.4RM.ndjson)
- trace.ndjson.BUG-4RM.VEA (use conf.16RM.ndjson)

