
import os
import time
import signal
from subprocess import Popen

print("# Start pipeline.")

print("# Start implementation.")

print("--- Run server ---")
server_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java", 
    "-XX:StartFlightRecording=disk=true,dumponexit=true,maxsize=20M,filename=app-server.jfr",
    "-cp", 
    "impl/out/production/TwoPhase",
    "org.lbee.twophase.Server",
    "6869"])

# Wait the server run, if comment this line, maye some manager running before the server, leading to error
# This behavior might be interesting for trace validation
time.sleep(5)

print("--- Run TM client ---")
tm_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java",
    "-XX:StartFlightRecording=disk=true,dumponexit=true,maxsize=20M,filename=app-tm.jfr",
    "-cp",
    "/home/me/.m2/repository/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar:impl/out/production/TwoPhase",
    "org.lbee.twophase.Client",
    "localhost", "6869", "tm"])

print("--- Run RM clients ---")
rm_processes = []
for i in range(2):
    print(f"Run rm{i} client")
    rm_process = Popen([
        "/usr/lib/jvm/jdk-19/bin/java",
        f"-XX:StartFlightRecording=disk=true,dumponexit=true,maxsize=20M,filename=app-rm-{i}.jfr",
        "-cp",
        "/home/me/.m2/repository/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar:impl/out/production/TwoPhase",
        "org.lbee.twophase.Client",
        "localhost", "6869", "rm"])

    rm_processes.append(rm_process)

# print(result.stdout.decode('utf-8'))

# Wait all client are finished
tm_process.wait()
for rm_process in rm_processes:
    rm_process.wait()

server_process.terminate()
tm_process.terminate()
for rm_process in rm_processes:
    rm_process.terminate()

# Kill server
os.kill(server_process.pid, signal.SIGINT)

print("# Start printing events.")

print_event_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java",
    "-cp",
    "impl/out/production/TwoPhase",
    "org.lbee.tools.JFRPrinter",
    "app-tm.jfr", "app-rm-0.jfr", "app-rm-1.jfr"])

print_event_process.wait()

print("# Start serializing events.")

# /usr/lib/jvm/jdk-19/bin/java -cp impl/out/production/TwoPhase org.lbee.tools.JFRSerializer app-tm.jfr app-rm-0.jfr app-rm-1.jfr

serializer_event_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java",
    "-cp",
    "/opt/TLAToolbox-1.7.1/toolbox/tla2tools.jar:/home/me/.m2/repository/com/google/code/gson/gson/2.10.1/gson-2.10.1.jar:impl/out/production/TwoPhase",
    "org.lbee.tools.JFRSerializer",
    "app-tm.jfr", "app-rm-0.jfr", "app-rm-1.jfr"])

serializer_event_process.wait()

print("# Start TLA+ trace spec.")

# java -cp /opt/TLAToolbox-1.7.1/toolbox/tla2tools.jar:CommunityModules.jar tlc2.TLC TwoPhaseTrace -deadlock

tla_trace_validation_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java",
    "-cp",
    "/opt/TLAToolbox-1.7.1/toolbox/tla2tools.jar:CommunityModules.jar",
    "tlc2.TLC",
    "TwoPhaseTrace_v5a", "-deadlock"])

tla_trace_validation_process.wait()

print("End pipeline.")