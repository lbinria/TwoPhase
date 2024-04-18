### Create (and check) a trace for 4 RMs

python trace_validation_pipeline.py --config BenchMarks/conf.4RM.ndjson 


### Check one of the traces

Run the script `tla_trace_validation.py` on one of the trace files; the trace file should be consistent with the conf file:
`trace.ndjson.4RM.VEA` with  `conf.4RM.ndjson`

`python tla_trace_validation.py --trace BenchMarks/trace.ndjson.4RM.VEA  --config BenchMarks/conf.4RM.ndjson spec/TwoPhaseTrace.tla`

Invalid trace:
 
`python tla_trace_validation.py --trace BenchMarks/trace.ndjson.BUG-4RM.VAE --config BenchMarks/conf.4RM.ndjson spec/TwoPhaseTrace.tla`

