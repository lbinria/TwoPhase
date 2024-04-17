python trace_validation_pipeline.py --config BenchMarks/conf.4RM.ndjson 

python tla_trace_validation.py --trace BenchMarks/trace.ndjson.5RM.VEA  --config BenchMarks/conf.5RM.ndjson spec/TwoPhaseTrace.tla

python tla_trace_validation.py --trace BenchMarks/trace.ndjson.BUG-4RM.VAE --config BenchMarks/conf.4RM.ndjson spec/TwoPhaseTrace.tla

