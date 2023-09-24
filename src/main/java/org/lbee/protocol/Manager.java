package org.lbee.protocol;
import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.network.NetworkManager;
import java.io.*;

public abstract class Manager {
    private final String name;
    public final NetworkManager networkManager;

    protected final BehaviorRecorder spec;
    protected final VirtualField specMessages;

    private boolean shutdown;

    public String getName() {
        return name;
    }

    /**
     * The manager has been shutdown?
     * 
     * @return True if manager has been shutdown
     */
    public boolean isShutdown() {
        return shutdown;
    }

    /**
     * Shutdown the manager
     */
    protected void shutdown() {
        System.out.println("-- "+this.name + " shutdown");
        shutdown = true;
    }

    public Manager(String name, NetworkManager networkManager, BehaviorRecorder spec) {
        this.name = name;
        this.networkManager = networkManager;
        this.shutdown = false;

        this.spec = spec;
        this.specMessages = spec.getVariable("msgs");
    }

    public abstract void run() throws IOException;
}
