
import os
import time
import signal
from subprocess import Popen

print("# Start pipeline.")

print("--- Run server ---")
server_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java", 
    "-XX:StartFlightRecording=disk=true,dumponexit=true,maxsize=20M,filename=app-server.jfr",
    "-cp", 
    "impl/out/production/TwoPhase",
    "org.lbee.twophase.Server",
    "6869"])

# Wait the server run
time.sleep(5)

print("--- Run TM client ---")
tm_process = Popen([
    "/usr/lib/jvm/jdk-19/bin/java",
    "-XX:StartFlightRecording=disk=true,dumponexit=true,maxsize=20M,filename=app-tm.jfr",
    "-cp",
    "impl/out/production/TwoPhase",
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
        "impl/out/production/TwoPhase",
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
print("End pipeline.")