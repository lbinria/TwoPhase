import os
import argparse
from subprocess import Popen

# Path to TLA installation
# tla_dir = "/opt/TLAToolbox-1.8.0-nightly/toolbox"
tla_dir = "/Users/cirstea/bin/TLA/"
tla_jar = os.path.join(tla_dir, "tla2tools.jar")
community_modules_jar = os.path.join(tla_dir, "CommunityModules-deps.jar")
tla_cp = f"{tla_jar}:{community_modules_jar}"

# Run TLC
# use "-Dtlc2.tool.queue.IStateQueue=StateDeque" for depth-first search
def run_tla(trace_spec,trace="trace.ndjson",config="conf.ndjson"):
    os.environ["TRACE_PATH"] = trace
    os.environ["CONFIG_PATH"] = config
    tla_trace_validation_process = Popen([
        "java",
        "-XX:+UseParallelGC",
        "-cp",
        tla_cp,
        "tlc2.TLC",
        trace_spec])
    tla_trace_validation_process.wait()
    tla_trace_validation_process.terminate()

if __name__ == "__main__":
    # Read program args
    parser = argparse.ArgumentParser(description="")
    parser.add_argument('spec', type=str, help="Specification file")
    parser.add_argument('--trace', type=str, required=False, default="trace.ndjson", help="Trace file")
    parser.add_argument('--config', type=str, required=False, default="conf.ndjson", help="Config file")
    args = parser.parse_args()
    # Run
    run_tla(args.spec,args.trace,args.config)

