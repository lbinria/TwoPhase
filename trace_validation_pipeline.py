import os
import subprocess
import run_impl
import trace_merger
import tla_trace_validation
import argparse

parser = argparse.ArgumentParser(
    prog='Trace validation pipeline',
    description='This program aims to execute a pipeline that validate implementation of KeyValueStore against a formal spec.')

parser.add_argument('-c', '--compile', type=bool, action=argparse.BooleanOptionalAction)

args = parser.parse_args()

print("# Clean up")

trace_files = [f for f in os.listdir(".") if f.endswith('.ndjson')]
print(f"Cleanup: {trace_files}")
for trace_file in trace_files:
    os.remove(trace_file)

if args.compile:
    print("# Package.\n")
    subprocess.run(["mvn", "package"])

print("# Start implementation.\n")

run_impl.run()

print("# Merge trace with config.\n")

trace_tla = trace_merger.run(["."], config="twophase.ndjson.conf", sort=True, remove_meta=True)
# Write to file
with open("trace-tla.ndjson", "w") as f:
    f.write(trace_tla)

print("# Start TLA+ trace spec.\n")

tla_trace_validation.run_tla("spec/TwoPhaseTrace.tla","trace-tla.ndjson","twophase.ndjson.conf")

print("End pipeline.")