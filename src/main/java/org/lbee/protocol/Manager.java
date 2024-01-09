package org.lbee.protocol;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.network.NetworkManager;
import java.io.*;

public abstract class Manager {
    private final String name;
    public final NetworkManager networkManager;
    protected final TLATracer tracer;

    public String getName() {
        return name;
    }

    public Manager(String name, NetworkManager networkManager, TLATracer tracer) {
        this.name = name;
        this.networkManager = networkManager;

        this.tracer = tracer;
    }

    public abstract void run() throws IOException;
}
