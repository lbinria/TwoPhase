# TwoPhase

Very simple implementation of 2PC protocol in Java.

## Compile

Requirements:
 - CommunityModules.jar (from TLA community)
 - ant
 - JDK (>= 19.0.2)


`sh two_phase_build.sh`

## Run 

Use following command line:
`python trace_validation_pipeline.py`

Run the pipeline:

 - Run implementation of 2PC protocol
 - Print logged events of implementation
 - Serialize logged events of implementation to binary file `Trace.bin`
 - Run TLA+ trace validation specification on previously serialized file