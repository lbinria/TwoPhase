import subprocess

print("Start pipeline.")

print("Run implementation...")

result = subprocess.run([
    "/usr/lib/jvm/jdk-19/bin/java", 
    "-XX:StartFlightRecording=disk=true,dumponexit=true,filename=app.jfr",
    "-cp", 
    "impl/out/production/twophase", 
    "org.lbee.twophase.App"], 
    capture_output=True)

print(result.stdout.decode('utf-8'))

print("OK.")

subprocess.run([""])


print("End pipeline.")