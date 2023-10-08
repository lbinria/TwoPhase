package org.lbee.protocol;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.network.NetworkManager;
import java.io.*;

public abstract class Manager {
    private final String name;
    public final NetworkManager networkManager;
    protected final TLATracer tracer;
    private boolean shutdown;

    public String getName() {
        return name;
    }

    /**
     * The manager has been shutdown?
     * 
     * @return True if manager has been shutdown
     */
    public boolean isTerminated() {
        return shutdown;
    }

    /**
     * Shutdown the manager
     */
    protected void terminate() {
        System.out.println("-- "+this.name + " shutdown");
        shutdown = true;
    }

    public Manager(String name, NetworkManager networkManager, TLATracer tracer) {
        this.name = name;
        this.networkManager = networkManager;
        this.shutdown = false;

        this.tracer = tracer;
    }

    public abstract void run() throws IOException;
}
